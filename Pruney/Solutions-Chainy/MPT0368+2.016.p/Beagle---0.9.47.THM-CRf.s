%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:50 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   54 (  97 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 221 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_32,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( m1_subset_1(B_16,A_15)
      | ~ v1_xboole_0(B_16)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    ! [C_22] :
      ( r2_hidden(C_22,'#skF_5')
      | ~ m1_subset_1(C_22,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_125,plain,(
    ! [A_52,B_53] :
      ( ~ r2_hidden('#skF_2'(A_52,B_53),B_53)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_172,plain,(
    ! [A_59] :
      ( r1_tarski(A_59,'#skF_5')
      | ~ m1_subset_1('#skF_2'(A_59,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_125])).

tff(c_176,plain,(
    ! [A_59] :
      ( r1_tarski(A_59,'#skF_5')
      | ~ v1_xboole_0('#skF_2'(A_59,'#skF_5'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_172])).

tff(c_299,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_96,plain,(
    ! [B_48,A_49] :
      ( m1_subset_1(B_48,A_49)
      | ~ r2_hidden(B_48,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_468,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1('#skF_2'(A_92,B_93),A_92)
      | v1_xboole_0(A_92)
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_10,c_96])).

tff(c_135,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,'#skF_5')
      | ~ m1_subset_1('#skF_2'(A_52,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_125])).

tff(c_476,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_468,c_135])).

tff(c_485,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_299,c_476])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_xboole_0(A_10,B_11)
      | B_11 = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),B_13)
      | ~ r2_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_256,plain,(
    ! [C_68,A_69,B_70] :
      ( r2_hidden(C_68,A_69)
      | ~ r2_hidden(C_68,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_726,plain,(
    ! [A_131,B_132,A_133] :
      ( r2_hidden('#skF_3'(A_131,B_132),A_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_133))
      | ~ r2_xboole_0(A_131,B_132) ) ),
    inference(resolution,[status(thm)],[c_20,c_256])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( ~ r2_hidden('#skF_3'(A_12,B_13),A_12)
      | ~ r2_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_746,plain,(
    ! [B_134,A_135] :
      ( ~ m1_subset_1(B_134,k1_zfmisc_1(A_135))
      | ~ r2_xboole_0(A_135,B_134) ) ),
    inference(resolution,[status(thm)],[c_726,c_18])).

tff(c_775,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_746])).

tff(c_778,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_775])).

tff(c_781,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_778])).

tff(c_783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_781])).

tff(c_785,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_789,plain,(
    ! [C_136,A_137] :
      ( r2_hidden(C_136,A_137)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_137))
      | ~ m1_subset_1(C_136,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_256])).

tff(c_803,plain,(
    ! [C_139] :
      ( r2_hidden(C_139,'#skF_4')
      | ~ m1_subset_1(C_139,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_789])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_821,plain,(
    ! [C_139] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_139,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_803,c_2])).

tff(c_831,plain,(
    ! [C_140] : ~ m1_subset_1(C_140,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_821])).

tff(c_839,plain,(
    ! [B_16] :
      ( ~ v1_xboole_0(B_16)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_831])).

tff(c_844,plain,(
    ! [B_16] : ~ v1_xboole_0(B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_839])).

tff(c_853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_844,c_785])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:08:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.39  
% 2.97/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.40  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.97/1.40  
% 2.97/1.40  %Foreground sorts:
% 2.97/1.40  
% 2.97/1.40  
% 2.97/1.40  %Background operators:
% 2.97/1.40  
% 2.97/1.40  
% 2.97/1.40  %Foreground operators:
% 2.97/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.97/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.97/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.97/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.40  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.97/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.97/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.97/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.40  
% 2.97/1.41  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 2.97/1.41  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.97/1.41  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.97/1.41  tff(f_45, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.97/1.41  tff(f_55, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.97/1.41  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.97/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.97/1.41  tff(c_32, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.97/1.41  tff(c_26, plain, (![B_16, A_15]: (m1_subset_1(B_16, A_15) | ~v1_xboole_0(B_16) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.97/1.41  tff(c_34, plain, (![C_22]: (r2_hidden(C_22, '#skF_5') | ~m1_subset_1(C_22, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.97/1.41  tff(c_125, plain, (![A_52, B_53]: (~r2_hidden('#skF_2'(A_52, B_53), B_53) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.97/1.41  tff(c_172, plain, (![A_59]: (r1_tarski(A_59, '#skF_5') | ~m1_subset_1('#skF_2'(A_59, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_125])).
% 2.97/1.41  tff(c_176, plain, (![A_59]: (r1_tarski(A_59, '#skF_5') | ~v1_xboole_0('#skF_2'(A_59, '#skF_5')) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_172])).
% 2.97/1.41  tff(c_299, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_176])).
% 2.97/1.41  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.97/1.41  tff(c_96, plain, (![B_48, A_49]: (m1_subset_1(B_48, A_49) | ~r2_hidden(B_48, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.97/1.41  tff(c_468, plain, (![A_92, B_93]: (m1_subset_1('#skF_2'(A_92, B_93), A_92) | v1_xboole_0(A_92) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_10, c_96])).
% 2.97/1.41  tff(c_135, plain, (![A_52]: (r1_tarski(A_52, '#skF_5') | ~m1_subset_1('#skF_2'(A_52, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_125])).
% 2.97/1.41  tff(c_476, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_468, c_135])).
% 2.97/1.41  tff(c_485, plain, (r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_299, c_476])).
% 2.97/1.41  tff(c_12, plain, (![A_10, B_11]: (r2_xboole_0(A_10, B_11) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.97/1.41  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.97/1.41  tff(c_20, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), B_13) | ~r2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.97/1.41  tff(c_256, plain, (![C_68, A_69, B_70]: (r2_hidden(C_68, A_69) | ~r2_hidden(C_68, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.97/1.41  tff(c_726, plain, (![A_131, B_132, A_133]: (r2_hidden('#skF_3'(A_131, B_132), A_133) | ~m1_subset_1(B_132, k1_zfmisc_1(A_133)) | ~r2_xboole_0(A_131, B_132))), inference(resolution, [status(thm)], [c_20, c_256])).
% 2.97/1.41  tff(c_18, plain, (![A_12, B_13]: (~r2_hidden('#skF_3'(A_12, B_13), A_12) | ~r2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.97/1.41  tff(c_746, plain, (![B_134, A_135]: (~m1_subset_1(B_134, k1_zfmisc_1(A_135)) | ~r2_xboole_0(A_135, B_134))), inference(resolution, [status(thm)], [c_726, c_18])).
% 2.97/1.41  tff(c_775, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_746])).
% 2.97/1.41  tff(c_778, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_12, c_775])).
% 2.97/1.41  tff(c_781, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_485, c_778])).
% 2.97/1.41  tff(c_783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_781])).
% 2.97/1.41  tff(c_785, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_176])).
% 2.97/1.41  tff(c_789, plain, (![C_136, A_137]: (r2_hidden(C_136, A_137) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_137)) | ~m1_subset_1(C_136, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_256])).
% 2.97/1.41  tff(c_803, plain, (![C_139]: (r2_hidden(C_139, '#skF_4') | ~m1_subset_1(C_139, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_789])).
% 2.97/1.41  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.41  tff(c_821, plain, (![C_139]: (~v1_xboole_0('#skF_4') | ~m1_subset_1(C_139, '#skF_4'))), inference(resolution, [status(thm)], [c_803, c_2])).
% 2.97/1.41  tff(c_831, plain, (![C_140]: (~m1_subset_1(C_140, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_785, c_821])).
% 2.97/1.41  tff(c_839, plain, (![B_16]: (~v1_xboole_0(B_16) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_831])).
% 2.97/1.41  tff(c_844, plain, (![B_16]: (~v1_xboole_0(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_785, c_839])).
% 2.97/1.41  tff(c_853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_844, c_785])).
% 2.97/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.41  
% 2.97/1.41  Inference rules
% 2.97/1.41  ----------------------
% 2.97/1.41  #Ref     : 0
% 2.97/1.41  #Sup     : 166
% 2.97/1.41  #Fact    : 0
% 2.97/1.41  #Define  : 0
% 2.97/1.41  #Split   : 4
% 2.97/1.41  #Chain   : 0
% 2.97/1.41  #Close   : 0
% 2.97/1.41  
% 2.97/1.41  Ordering : KBO
% 2.97/1.41  
% 2.97/1.41  Simplification rules
% 2.97/1.41  ----------------------
% 2.97/1.41  #Subsume      : 89
% 2.97/1.41  #Demod        : 10
% 2.97/1.41  #Tautology    : 24
% 2.97/1.41  #SimpNegUnit  : 38
% 2.97/1.41  #BackRed      : 11
% 2.97/1.41  
% 2.97/1.41  #Partial instantiations: 0
% 2.97/1.41  #Strategies tried      : 1
% 2.97/1.41  
% 2.97/1.41  Timing (in seconds)
% 2.97/1.41  ----------------------
% 2.97/1.41  Preprocessing        : 0.29
% 2.97/1.41  Parsing              : 0.16
% 2.97/1.41  CNF conversion       : 0.02
% 2.97/1.41  Main loop            : 0.36
% 2.97/1.41  Inferencing          : 0.14
% 2.97/1.41  Reduction            : 0.08
% 2.97/1.41  Demodulation         : 0.05
% 2.97/1.41  BG Simplification    : 0.02
% 2.97/1.41  Subsumption          : 0.09
% 2.97/1.41  Abstraction          : 0.01
% 2.97/1.41  MUC search           : 0.00
% 2.97/1.41  Cooper               : 0.00
% 2.97/1.41  Total                : 0.69
% 2.97/1.41  Index Insertion      : 0.00
% 2.97/1.41  Index Deletion       : 0.00
% 2.97/1.41  Index Matching       : 0.00
% 2.97/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
