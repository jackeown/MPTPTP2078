%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:16 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   52 (  94 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 221 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                   => r2_hidden(D,C) ) )
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_22,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_75,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_2'(A_34,B_35),A_34)
      | r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_39,B_40] :
      ( ~ v1_xboole_0(A_39)
      | r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_75,c_2])).

tff(c_108,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_22])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( m1_subset_1(B_11,A_10)
      | ~ r2_hidden(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_87,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1('#skF_2'(A_34,B_35),A_34)
      | v1_xboole_0(A_34)
      | r1_tarski(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_75,c_12])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_144,plain,(
    ! [C_48,A_49,B_50] :
      ( r2_hidden(C_48,A_49)
      | ~ r2_hidden(C_48,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_165,plain,(
    ! [A_53,A_54] :
      ( r2_hidden('#skF_1'(A_53),A_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(A_54))
      | v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_4,c_144])).

tff(c_180,plain,(
    ! [A_55,A_56] :
      ( ~ v1_xboole_0(A_55)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(A_55))
      | v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_165,c_2])).

tff(c_198,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_180])).

tff(c_207,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_198])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_704,plain,(
    ! [A_107,B_108,A_109] :
      ( r2_hidden('#skF_2'(A_107,B_108),A_109)
      | ~ m1_subset_1(A_107,k1_zfmisc_1(A_109))
      | r1_tarski(A_107,B_108) ) ),
    inference(resolution,[status(thm)],[c_10,c_144])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_738,plain,(
    ! [A_111,A_112] :
      ( ~ m1_subset_1(A_111,k1_zfmisc_1(A_112))
      | r1_tarski(A_111,A_112) ) ),
    inference(resolution,[status(thm)],[c_704,c_8])).

tff(c_771,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_738])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r2_hidden(B_11,A_10)
      | ~ m1_subset_1(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_110,plain,(
    ! [C_41,B_42,A_43] :
      ( r2_hidden(C_41,B_42)
      | ~ r2_hidden(C_41,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_119,plain,(
    ! [B_11,B_42,A_10] :
      ( r2_hidden(B_11,B_42)
      | ~ r1_tarski(A_10,B_42)
      | ~ m1_subset_1(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_110])).

tff(c_797,plain,(
    ! [B_11] :
      ( r2_hidden(B_11,'#skF_3')
      | ~ m1_subset_1(B_11,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_771,c_119])).

tff(c_811,plain,(
    ! [B_113] :
      ( r2_hidden(B_113,'#skF_3')
      | ~ m1_subset_1(B_113,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_797])).

tff(c_822,plain,(
    ! [B_113] :
      ( m1_subset_1(B_113,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_113,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_811,c_12])).

tff(c_831,plain,(
    ! [B_113] :
      ( m1_subset_1(B_113,'#skF_3')
      | ~ m1_subset_1(B_113,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_822])).

tff(c_24,plain,(
    ! [D_20] :
      ( r2_hidden(D_20,'#skF_5')
      | ~ r2_hidden(D_20,'#skF_4')
      | ~ m1_subset_1(D_20,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_69,plain,(
    ! [A_32,B_33] :
      ( ~ r2_hidden('#skF_2'(A_32,B_33),B_33)
      | r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1084,plain,(
    ! [A_132] :
      ( r1_tarski(A_132,'#skF_5')
      | ~ r2_hidden('#skF_2'(A_132,'#skF_5'),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_132,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_69])).

tff(c_1102,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_1084])).

tff(c_1111,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_22,c_1102])).

tff(c_1118,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_831,c_1111])).

tff(c_1122,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_87,c_1118])).

tff(c_1129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_108,c_1122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.52  
% 3.16/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.52  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.16/1.52  
% 3.16/1.52  %Foreground sorts:
% 3.16/1.52  
% 3.16/1.52  
% 3.16/1.52  %Background operators:
% 3.16/1.52  
% 3.16/1.52  
% 3.16/1.52  %Foreground operators:
% 3.16/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.16/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.16/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.16/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.52  
% 3.16/1.53  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 3.16/1.53  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.16/1.53  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.16/1.53  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.16/1.53  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.16/1.53  tff(c_22, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.16/1.53  tff(c_75, plain, (![A_34, B_35]: (r2_hidden('#skF_2'(A_34, B_35), A_34) | r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.16/1.53  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.53  tff(c_104, plain, (![A_39, B_40]: (~v1_xboole_0(A_39) | r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_75, c_2])).
% 3.16/1.53  tff(c_108, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_104, c_22])).
% 3.16/1.53  tff(c_12, plain, (![B_11, A_10]: (m1_subset_1(B_11, A_10) | ~r2_hidden(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.16/1.53  tff(c_87, plain, (![A_34, B_35]: (m1_subset_1('#skF_2'(A_34, B_35), A_34) | v1_xboole_0(A_34) | r1_tarski(A_34, B_35))), inference(resolution, [status(thm)], [c_75, c_12])).
% 3.16/1.53  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.16/1.53  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.53  tff(c_144, plain, (![C_48, A_49, B_50]: (r2_hidden(C_48, A_49) | ~r2_hidden(C_48, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.16/1.53  tff(c_165, plain, (![A_53, A_54]: (r2_hidden('#skF_1'(A_53), A_54) | ~m1_subset_1(A_53, k1_zfmisc_1(A_54)) | v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_4, c_144])).
% 3.16/1.53  tff(c_180, plain, (![A_55, A_56]: (~v1_xboole_0(A_55) | ~m1_subset_1(A_56, k1_zfmisc_1(A_55)) | v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_165, c_2])).
% 3.16/1.53  tff(c_198, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_28, c_180])).
% 3.16/1.53  tff(c_207, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_108, c_198])).
% 3.16/1.53  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.16/1.53  tff(c_704, plain, (![A_107, B_108, A_109]: (r2_hidden('#skF_2'(A_107, B_108), A_109) | ~m1_subset_1(A_107, k1_zfmisc_1(A_109)) | r1_tarski(A_107, B_108))), inference(resolution, [status(thm)], [c_10, c_144])).
% 3.16/1.53  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.16/1.53  tff(c_738, plain, (![A_111, A_112]: (~m1_subset_1(A_111, k1_zfmisc_1(A_112)) | r1_tarski(A_111, A_112))), inference(resolution, [status(thm)], [c_704, c_8])).
% 3.16/1.53  tff(c_771, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_738])).
% 3.16/1.53  tff(c_14, plain, (![B_11, A_10]: (r2_hidden(B_11, A_10) | ~m1_subset_1(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.16/1.53  tff(c_110, plain, (![C_41, B_42, A_43]: (r2_hidden(C_41, B_42) | ~r2_hidden(C_41, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.16/1.53  tff(c_119, plain, (![B_11, B_42, A_10]: (r2_hidden(B_11, B_42) | ~r1_tarski(A_10, B_42) | ~m1_subset_1(B_11, A_10) | v1_xboole_0(A_10))), inference(resolution, [status(thm)], [c_14, c_110])).
% 3.16/1.53  tff(c_797, plain, (![B_11]: (r2_hidden(B_11, '#skF_3') | ~m1_subset_1(B_11, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_771, c_119])).
% 3.16/1.53  tff(c_811, plain, (![B_113]: (r2_hidden(B_113, '#skF_3') | ~m1_subset_1(B_113, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_108, c_797])).
% 3.16/1.53  tff(c_822, plain, (![B_113]: (m1_subset_1(B_113, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_113, '#skF_4'))), inference(resolution, [status(thm)], [c_811, c_12])).
% 3.16/1.53  tff(c_831, plain, (![B_113]: (m1_subset_1(B_113, '#skF_3') | ~m1_subset_1(B_113, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_207, c_822])).
% 3.16/1.53  tff(c_24, plain, (![D_20]: (r2_hidden(D_20, '#skF_5') | ~r2_hidden(D_20, '#skF_4') | ~m1_subset_1(D_20, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.16/1.53  tff(c_69, plain, (![A_32, B_33]: (~r2_hidden('#skF_2'(A_32, B_33), B_33) | r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.16/1.53  tff(c_1084, plain, (![A_132]: (r1_tarski(A_132, '#skF_5') | ~r2_hidden('#skF_2'(A_132, '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_2'(A_132, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_69])).
% 3.16/1.53  tff(c_1102, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_10, c_1084])).
% 3.16/1.53  tff(c_1111, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_22, c_22, c_1102])).
% 3.16/1.53  tff(c_1118, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_831, c_1111])).
% 3.16/1.53  tff(c_1122, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_87, c_1118])).
% 3.16/1.53  tff(c_1129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_108, c_1122])).
% 3.16/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.53  
% 3.16/1.53  Inference rules
% 3.16/1.53  ----------------------
% 3.16/1.53  #Ref     : 0
% 3.16/1.53  #Sup     : 237
% 3.16/1.53  #Fact    : 0
% 3.16/1.53  #Define  : 0
% 3.16/1.53  #Split   : 4
% 3.16/1.53  #Chain   : 0
% 3.16/1.53  #Close   : 0
% 3.16/1.53  
% 3.16/1.53  Ordering : KBO
% 3.16/1.53  
% 3.16/1.53  Simplification rules
% 3.16/1.53  ----------------------
% 3.16/1.53  #Subsume      : 62
% 3.16/1.53  #Demod        : 23
% 3.16/1.53  #Tautology    : 28
% 3.16/1.53  #SimpNegUnit  : 34
% 3.16/1.53  #BackRed      : 0
% 3.16/1.53  
% 3.16/1.53  #Partial instantiations: 0
% 3.16/1.53  #Strategies tried      : 1
% 3.16/1.53  
% 3.16/1.53  Timing (in seconds)
% 3.16/1.53  ----------------------
% 3.16/1.54  Preprocessing        : 0.30
% 3.16/1.54  Parsing              : 0.16
% 3.16/1.54  CNF conversion       : 0.02
% 3.16/1.54  Main loop            : 0.43
% 3.16/1.54  Inferencing          : 0.17
% 3.16/1.54  Reduction            : 0.11
% 3.16/1.54  Demodulation         : 0.06
% 3.16/1.54  BG Simplification    : 0.02
% 3.16/1.54  Subsumption          : 0.10
% 3.16/1.54  Abstraction          : 0.02
% 3.16/1.54  MUC search           : 0.00
% 3.16/1.54  Cooper               : 0.00
% 3.16/1.54  Total                : 0.76
% 3.28/1.54  Index Insertion      : 0.00
% 3.28/1.54  Index Deletion       : 0.00
% 3.28/1.54  Index Matching       : 0.00
% 3.28/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
