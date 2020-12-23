%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:50 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 139 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 328 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

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

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(c_30,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [B_35,A_36] :
      ( m1_subset_1(B_35,A_36)
      | ~ r2_hidden(B_35,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_72,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_62])).

tff(c_44,plain,(
    ! [C_30] :
      ( r2_hidden(C_30,'#skF_4')
      | ~ m1_subset_1(C_30,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [C_30] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_30,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_49,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_32,plain,(
    ! [C_21] :
      ( r2_hidden(C_21,'#skF_4')
      | ~ m1_subset_1(C_21,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_65,plain,(
    ! [C_21] :
      ( m1_subset_1(C_21,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_21,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_62])).

tff(c_84,plain,(
    ! [C_40] :
      ( m1_subset_1(C_40,'#skF_4')
      | ~ m1_subset_1(C_40,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_65])).

tff(c_93,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_84])).

tff(c_95,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( m1_subset_1(B_15,A_14)
      | ~ v1_xboole_0(B_15)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_288,plain,(
    ! [C_76,A_77,B_78] :
      ( r2_hidden(C_76,A_77)
      | ~ r2_hidden(C_76,B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_348,plain,(
    ! [C_83,A_84] :
      ( r2_hidden(C_83,A_84)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_84))
      | ~ m1_subset_1(C_83,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_288])).

tff(c_371,plain,(
    ! [C_87] :
      ( r2_hidden(C_87,'#skF_3')
      | ~ m1_subset_1(C_87,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_348])).

tff(c_385,plain,(
    ! [C_87] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ m1_subset_1(C_87,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_371,c_2])).

tff(c_394,plain,(
    ! [C_88] : ~ m1_subset_1(C_88,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_385])).

tff(c_406,plain,(
    ! [B_15] :
      ( ~ v1_xboole_0(B_15)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_394])).

tff(c_413,plain,(
    ! [B_15] : ~ v1_xboole_0(B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_406])).

tff(c_425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_95])).

tff(c_427,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_466,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_2'(A_94,B_95),A_94)
      | r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( m1_subset_1(B_15,A_14)
      | ~ r2_hidden(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_626,plain,(
    ! [A_126,B_127] :
      ( m1_subset_1('#skF_2'(A_126,B_127),A_126)
      | v1_xboole_0(A_126)
      | r1_tarski(A_126,B_127) ) ),
    inference(resolution,[status(thm)],[c_466,c_20])).

tff(c_78,plain,(
    ! [A_38,B_39] :
      ( ~ r2_hidden('#skF_2'(A_38,B_39),B_39)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_83,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_38,'#skF_4'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_78])).

tff(c_638,plain,
    ( v1_xboole_0('#skF_3')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_626,c_83])).

tff(c_653,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_638])).

tff(c_437,plain,(
    ! [A_90,B_91] :
      ( r2_xboole_0(A_90,B_91)
      | B_91 = A_90
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( ~ r2_xboole_0(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_449,plain,(
    ! [B_91,A_90] :
      ( ~ r1_tarski(B_91,A_90)
      | B_91 = A_90
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_437,c_18])).

tff(c_665,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_653,c_449])).

tff(c_672,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_665])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_601,plain,(
    ! [C_121,A_122,B_123] :
      ( r2_hidden(C_121,A_122)
      | ~ r2_hidden(C_121,B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_926,plain,(
    ! [A_159,B_160,A_161] :
      ( r2_hidden('#skF_2'(A_159,B_160),A_161)
      | ~ m1_subset_1(A_159,k1_zfmisc_1(A_161))
      | r1_tarski(A_159,B_160) ) ),
    inference(resolution,[status(thm)],[c_10,c_601])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_946,plain,(
    ! [A_162,A_163] :
      ( ~ m1_subset_1(A_162,k1_zfmisc_1(A_163))
      | r1_tarski(A_162,A_163) ) ),
    inference(resolution,[status(thm)],[c_926,c_8])).

tff(c_961,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_946])).

tff(c_968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_672,c_961])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:34:15 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.51  
% 2.96/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.51  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.96/1.51  
% 2.96/1.51  %Foreground sorts:
% 2.96/1.51  
% 2.96/1.51  
% 2.96/1.51  %Background operators:
% 2.96/1.51  
% 2.96/1.51  
% 2.96/1.51  %Foreground operators:
% 2.96/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.96/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.51  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.96/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.51  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.96/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.96/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.51  
% 2.96/1.53  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 2.96/1.53  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.96/1.53  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.96/1.53  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.96/1.53  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.96/1.53  tff(f_45, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.96/1.53  tff(f_50, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.96/1.53  tff(c_30, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.96/1.53  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.53  tff(c_62, plain, (![B_35, A_36]: (m1_subset_1(B_35, A_36) | ~r2_hidden(B_35, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.96/1.53  tff(c_72, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_62])).
% 2.96/1.53  tff(c_44, plain, (![C_30]: (r2_hidden(C_30, '#skF_4') | ~m1_subset_1(C_30, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.96/1.53  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.53  tff(c_48, plain, (![C_30]: (~v1_xboole_0('#skF_4') | ~m1_subset_1(C_30, '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_2])).
% 2.96/1.53  tff(c_49, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 2.96/1.53  tff(c_32, plain, (![C_21]: (r2_hidden(C_21, '#skF_4') | ~m1_subset_1(C_21, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.96/1.53  tff(c_65, plain, (![C_21]: (m1_subset_1(C_21, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(C_21, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_62])).
% 2.96/1.53  tff(c_84, plain, (![C_40]: (m1_subset_1(C_40, '#skF_4') | ~m1_subset_1(C_40, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_49, c_65])).
% 2.96/1.53  tff(c_93, plain, (m1_subset_1('#skF_1'('#skF_3'), '#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_72, c_84])).
% 2.96/1.53  tff(c_95, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_93])).
% 2.96/1.53  tff(c_24, plain, (![B_15, A_14]: (m1_subset_1(B_15, A_14) | ~v1_xboole_0(B_15) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.96/1.53  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.96/1.53  tff(c_288, plain, (![C_76, A_77, B_78]: (r2_hidden(C_76, A_77) | ~r2_hidden(C_76, B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.96/1.53  tff(c_348, plain, (![C_83, A_84]: (r2_hidden(C_83, A_84) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_84)) | ~m1_subset_1(C_83, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_288])).
% 2.96/1.53  tff(c_371, plain, (![C_87]: (r2_hidden(C_87, '#skF_3') | ~m1_subset_1(C_87, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_348])).
% 2.96/1.53  tff(c_385, plain, (![C_87]: (~v1_xboole_0('#skF_3') | ~m1_subset_1(C_87, '#skF_3'))), inference(resolution, [status(thm)], [c_371, c_2])).
% 2.96/1.53  tff(c_394, plain, (![C_88]: (~m1_subset_1(C_88, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_385])).
% 2.96/1.53  tff(c_406, plain, (![B_15]: (~v1_xboole_0(B_15) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_394])).
% 2.96/1.53  tff(c_413, plain, (![B_15]: (~v1_xboole_0(B_15))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_406])).
% 2.96/1.53  tff(c_425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_413, c_95])).
% 2.96/1.53  tff(c_427, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_93])).
% 2.96/1.53  tff(c_466, plain, (![A_94, B_95]: (r2_hidden('#skF_2'(A_94, B_95), A_94) | r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.96/1.53  tff(c_20, plain, (![B_15, A_14]: (m1_subset_1(B_15, A_14) | ~r2_hidden(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.96/1.53  tff(c_626, plain, (![A_126, B_127]: (m1_subset_1('#skF_2'(A_126, B_127), A_126) | v1_xboole_0(A_126) | r1_tarski(A_126, B_127))), inference(resolution, [status(thm)], [c_466, c_20])).
% 2.96/1.53  tff(c_78, plain, (![A_38, B_39]: (~r2_hidden('#skF_2'(A_38, B_39), B_39) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.96/1.53  tff(c_83, plain, (![A_38]: (r1_tarski(A_38, '#skF_4') | ~m1_subset_1('#skF_2'(A_38, '#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_78])).
% 2.96/1.53  tff(c_638, plain, (v1_xboole_0('#skF_3') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_626, c_83])).
% 2.96/1.53  tff(c_653, plain, (r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_427, c_638])).
% 2.96/1.53  tff(c_437, plain, (![A_90, B_91]: (r2_xboole_0(A_90, B_91) | B_91=A_90 | ~r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.96/1.53  tff(c_18, plain, (![B_13, A_12]: (~r2_xboole_0(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.96/1.53  tff(c_449, plain, (![B_91, A_90]: (~r1_tarski(B_91, A_90) | B_91=A_90 | ~r1_tarski(A_90, B_91))), inference(resolution, [status(thm)], [c_437, c_18])).
% 2.96/1.53  tff(c_665, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_653, c_449])).
% 2.96/1.53  tff(c_672, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_665])).
% 2.96/1.53  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.96/1.53  tff(c_601, plain, (![C_121, A_122, B_123]: (r2_hidden(C_121, A_122) | ~r2_hidden(C_121, B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.96/1.53  tff(c_926, plain, (![A_159, B_160, A_161]: (r2_hidden('#skF_2'(A_159, B_160), A_161) | ~m1_subset_1(A_159, k1_zfmisc_1(A_161)) | r1_tarski(A_159, B_160))), inference(resolution, [status(thm)], [c_10, c_601])).
% 2.96/1.53  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.96/1.53  tff(c_946, plain, (![A_162, A_163]: (~m1_subset_1(A_162, k1_zfmisc_1(A_163)) | r1_tarski(A_162, A_163))), inference(resolution, [status(thm)], [c_926, c_8])).
% 2.96/1.53  tff(c_961, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_946])).
% 2.96/1.53  tff(c_968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_672, c_961])).
% 2.96/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.53  
% 2.96/1.53  Inference rules
% 2.96/1.53  ----------------------
% 2.96/1.53  #Ref     : 0
% 2.96/1.53  #Sup     : 193
% 2.96/1.53  #Fact    : 0
% 2.96/1.53  #Define  : 0
% 2.96/1.53  #Split   : 5
% 2.96/1.53  #Chain   : 0
% 2.96/1.53  #Close   : 0
% 2.96/1.53  
% 2.96/1.53  Ordering : KBO
% 2.96/1.53  
% 2.96/1.53  Simplification rules
% 2.96/1.53  ----------------------
% 2.96/1.53  #Subsume      : 91
% 2.96/1.53  #Demod        : 19
% 2.96/1.53  #Tautology    : 37
% 2.96/1.53  #SimpNegUnit  : 38
% 2.96/1.53  #BackRed      : 14
% 2.96/1.53  
% 2.96/1.53  #Partial instantiations: 0
% 2.96/1.53  #Strategies tried      : 1
% 2.96/1.53  
% 2.96/1.53  Timing (in seconds)
% 2.96/1.53  ----------------------
% 2.96/1.53  Preprocessing        : 0.27
% 2.96/1.53  Parsing              : 0.14
% 2.96/1.53  CNF conversion       : 0.02
% 2.96/1.53  Main loop            : 0.45
% 2.96/1.53  Inferencing          : 0.18
% 2.96/1.53  Reduction            : 0.10
% 2.96/1.53  Demodulation         : 0.06
% 2.96/1.53  BG Simplification    : 0.02
% 2.96/1.53  Subsumption          : 0.11
% 2.96/1.53  Abstraction          : 0.02
% 2.96/1.53  MUC search           : 0.00
% 2.96/1.53  Cooper               : 0.00
% 2.96/1.53  Total                : 0.75
% 2.96/1.53  Index Insertion      : 0.00
% 2.96/1.53  Index Deletion       : 0.00
% 2.96/1.53  Index Matching       : 0.00
% 2.96/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
