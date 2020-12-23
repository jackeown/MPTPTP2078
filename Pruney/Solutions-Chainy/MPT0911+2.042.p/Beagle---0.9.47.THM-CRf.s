%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:07 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 165 expanded)
%              Number of leaves         :   25 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          :  159 ( 790 expanded)
%              Number of equality atoms :  115 ( 506 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ? [D] :
            ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
            & ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ! [G] :
                        ( m1_subset_1(G,C)
                       => D != k3_mcart_1(E,F,G) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ? [E,F,G] :
              ( D = k3_mcart_1(E,F,G)
              & ~ ( k5_mcart_1(A,B,C,D) = E
                  & k6_mcart_1(A,B,C,D) = F
                  & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_66,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( k7_mcart_1(A_77,B_78,C_79,D_80) = k2_mcart_1(D_80)
      | ~ m1_subset_1(D_80,k3_zfmisc_1(A_77,B_78,C_79))
      | k1_xboole_0 = C_79
      | k1_xboole_0 = B_78
      | k1_xboole_0 = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_76,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_66])).

tff(c_80,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_76])).

tff(c_24,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_81,plain,(
    k2_mcart_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_24])).

tff(c_10,plain,(
    ! [A_4,B_5,C_6,D_22] :
      ( m1_subset_1('#skF_1'(A_4,B_5,C_6,D_22),A_4)
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,B_5,C_6))
      | k1_xboole_0 = C_6
      | k1_xboole_0 = B_5
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6,D_22] :
      ( m1_subset_1('#skF_3'(A_4,B_5,C_6,D_22),C_6)
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,B_5,C_6))
      | k1_xboole_0 = C_6
      | k1_xboole_0 = B_5
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_4,B_5,C_6,D_22] :
      ( m1_subset_1('#skF_2'(A_4,B_5,C_6,D_22),B_5)
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,B_5,C_6))
      | k1_xboole_0 = C_6
      | k1_xboole_0 = B_5
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_237,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( k3_mcart_1('#skF_1'(A_130,B_131,C_132,D_133),'#skF_2'(A_130,B_131,C_132,D_133),'#skF_3'(A_130,B_131,C_132,D_133)) = D_133
      | ~ m1_subset_1(D_133,k3_zfmisc_1(A_130,B_131,C_132))
      | k1_xboole_0 = C_132
      | k1_xboole_0 = B_131
      | k1_xboole_0 = A_130 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ! [H_62,F_56,G_60] :
      ( H_62 = '#skF_7'
      | k3_mcart_1(F_56,G_60,H_62) != '#skF_8'
      | ~ m1_subset_1(H_62,'#skF_6')
      | ~ m1_subset_1(G_60,'#skF_5')
      | ~ m1_subset_1(F_56,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_282,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( '#skF_3'(A_155,B_156,C_157,D_158) = '#skF_7'
      | D_158 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_155,B_156,C_157,D_158),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_155,B_156,C_157,D_158),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_155,B_156,C_157,D_158),'#skF_4')
      | ~ m1_subset_1(D_158,k3_zfmisc_1(A_155,B_156,C_157))
      | k1_xboole_0 = C_157
      | k1_xboole_0 = B_156
      | k1_xboole_0 = A_155 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_32])).

tff(c_286,plain,(
    ! [A_4,C_6,D_22] :
      ( '#skF_3'(A_4,'#skF_5',C_6,D_22) = '#skF_7'
      | D_22 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_4,'#skF_5',C_6,D_22),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_4,'#skF_5',C_6,D_22),'#skF_4')
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,'#skF_5',C_6))
      | k1_xboole_0 = C_6
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_4 ) ),
    inference(resolution,[status(thm)],[c_8,c_282])).

tff(c_291,plain,(
    ! [A_159,C_160,D_161] :
      ( '#skF_3'(A_159,'#skF_5',C_160,D_161) = '#skF_7'
      | D_161 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_159,'#skF_5',C_160,D_161),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_159,'#skF_5',C_160,D_161),'#skF_4')
      | ~ m1_subset_1(D_161,k3_zfmisc_1(A_159,'#skF_5',C_160))
      | k1_xboole_0 = C_160
      | k1_xboole_0 = A_159 ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_286])).

tff(c_295,plain,(
    ! [A_4,D_22] :
      ( '#skF_3'(A_4,'#skF_5','#skF_6',D_22) = '#skF_7'
      | D_22 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_4,'#skF_5','#skF_6',D_22),'#skF_4')
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,'#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_4 ) ),
    inference(resolution,[status(thm)],[c_6,c_291])).

tff(c_300,plain,(
    ! [A_162,D_163] :
      ( '#skF_3'(A_162,'#skF_5','#skF_6',D_163) = '#skF_7'
      | D_163 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_162,'#skF_5','#skF_6',D_163),'#skF_4')
      | ~ m1_subset_1(D_163,k3_zfmisc_1(A_162,'#skF_5','#skF_6'))
      | k1_xboole_0 = A_162 ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_26,c_295])).

tff(c_304,plain,(
    ! [D_22] :
      ( '#skF_3'('#skF_4','#skF_5','#skF_6',D_22) = '#skF_7'
      | D_22 != '#skF_8'
      | ~ m1_subset_1(D_22,k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_10,c_300])).

tff(c_309,plain,(
    ! [D_164] :
      ( '#skF_3'('#skF_4','#skF_5','#skF_6',D_164) = '#skF_7'
      | D_164 != '#skF_8'
      | ~ m1_subset_1(D_164,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_30,c_304])).

tff(c_328,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_34,c_309])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_22] :
      ( k3_mcart_1('#skF_1'(A_4,B_5,C_6,D_22),'#skF_2'(A_4,B_5,C_6,D_22),'#skF_3'(A_4,B_5,C_6,D_22)) = D_22
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,B_5,C_6))
      | k1_xboole_0 = C_6
      | k1_xboole_0 = B_5
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_335,plain,
    ( k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_4])).

tff(c_346,plain,
    ( k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7') = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_335])).

tff(c_347,plain,(
    k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_346])).

tff(c_18,plain,(
    ! [G_48,E_46,A_39,C_41,B_40,F_47] :
      ( k7_mcart_1(A_39,B_40,C_41,k3_mcart_1(E_46,F_47,G_48)) = G_48
      | k1_xboole_0 = C_41
      | k1_xboole_0 = B_40
      | k1_xboole_0 = A_39
      | ~ m1_subset_1(k3_mcart_1(E_46,F_47,G_48),k3_zfmisc_1(A_39,B_40,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_389,plain,(
    ! [A_39,B_40,C_41] :
      ( k7_mcart_1(A_39,B_40,C_41,k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7')) = '#skF_7'
      | k1_xboole_0 = C_41
      | k1_xboole_0 = B_40
      | k1_xboole_0 = A_39
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_39,B_40,C_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_18])).

tff(c_405,plain,(
    ! [A_171,B_172,C_173] :
      ( k7_mcart_1(A_171,B_172,C_173,'#skF_8') = '#skF_7'
      | k1_xboole_0 = C_173
      | k1_xboole_0 = B_172
      | k1_xboole_0 = A_171
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_171,B_172,C_173)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_389])).

tff(c_411,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_405])).

tff(c_413,plain,
    ( k2_mcart_1('#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_411])).

tff(c_415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_81,c_413])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:35:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.41  
% 2.70/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.41  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 2.70/1.41  
% 2.70/1.41  %Foreground sorts:
% 2.70/1.41  
% 2.70/1.41  
% 2.70/1.41  %Background operators:
% 2.70/1.41  
% 2.70/1.41  
% 2.70/1.41  %Foreground operators:
% 2.70/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.41  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.70/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.70/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.70/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.70/1.41  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.70/1.41  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.70/1.41  tff('#skF_8', type, '#skF_8': $i).
% 2.70/1.41  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.70/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.70/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.41  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.70/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.70/1.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.70/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.70/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.41  
% 2.70/1.43  tff(f_118, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 2.70/1.43  tff(f_72, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 2.70/1.43  tff(f_52, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_mcart_1)).
% 2.70/1.43  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[E, F, G]: ((D = k3_mcart_1(E, F, G)) & ~(((k5_mcart_1(A, B, C, D) = E) & (k6_mcart_1(A, B, C, D) = F)) & (k7_mcart_1(A, B, C, D) = G))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_mcart_1)).
% 2.70/1.43  tff(c_30, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.70/1.43  tff(c_28, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.70/1.43  tff(c_26, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.70/1.43  tff(c_34, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.70/1.43  tff(c_66, plain, (![A_77, B_78, C_79, D_80]: (k7_mcart_1(A_77, B_78, C_79, D_80)=k2_mcart_1(D_80) | ~m1_subset_1(D_80, k3_zfmisc_1(A_77, B_78, C_79)) | k1_xboole_0=C_79 | k1_xboole_0=B_78 | k1_xboole_0=A_77)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.70/1.43  tff(c_76, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_66])).
% 2.70/1.43  tff(c_80, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_76])).
% 2.70/1.43  tff(c_24, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.70/1.43  tff(c_81, plain, (k2_mcart_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_24])).
% 2.70/1.43  tff(c_10, plain, (![A_4, B_5, C_6, D_22]: (m1_subset_1('#skF_1'(A_4, B_5, C_6, D_22), A_4) | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, B_5, C_6)) | k1_xboole_0=C_6 | k1_xboole_0=B_5 | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.70/1.43  tff(c_6, plain, (![A_4, B_5, C_6, D_22]: (m1_subset_1('#skF_3'(A_4, B_5, C_6, D_22), C_6) | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, B_5, C_6)) | k1_xboole_0=C_6 | k1_xboole_0=B_5 | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.70/1.43  tff(c_8, plain, (![A_4, B_5, C_6, D_22]: (m1_subset_1('#skF_2'(A_4, B_5, C_6, D_22), B_5) | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, B_5, C_6)) | k1_xboole_0=C_6 | k1_xboole_0=B_5 | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.70/1.43  tff(c_237, plain, (![A_130, B_131, C_132, D_133]: (k3_mcart_1('#skF_1'(A_130, B_131, C_132, D_133), '#skF_2'(A_130, B_131, C_132, D_133), '#skF_3'(A_130, B_131, C_132, D_133))=D_133 | ~m1_subset_1(D_133, k3_zfmisc_1(A_130, B_131, C_132)) | k1_xboole_0=C_132 | k1_xboole_0=B_131 | k1_xboole_0=A_130)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.70/1.43  tff(c_32, plain, (![H_62, F_56, G_60]: (H_62='#skF_7' | k3_mcart_1(F_56, G_60, H_62)!='#skF_8' | ~m1_subset_1(H_62, '#skF_6') | ~m1_subset_1(G_60, '#skF_5') | ~m1_subset_1(F_56, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.70/1.43  tff(c_282, plain, (![A_155, B_156, C_157, D_158]: ('#skF_3'(A_155, B_156, C_157, D_158)='#skF_7' | D_158!='#skF_8' | ~m1_subset_1('#skF_3'(A_155, B_156, C_157, D_158), '#skF_6') | ~m1_subset_1('#skF_2'(A_155, B_156, C_157, D_158), '#skF_5') | ~m1_subset_1('#skF_1'(A_155, B_156, C_157, D_158), '#skF_4') | ~m1_subset_1(D_158, k3_zfmisc_1(A_155, B_156, C_157)) | k1_xboole_0=C_157 | k1_xboole_0=B_156 | k1_xboole_0=A_155)), inference(superposition, [status(thm), theory('equality')], [c_237, c_32])).
% 2.70/1.43  tff(c_286, plain, (![A_4, C_6, D_22]: ('#skF_3'(A_4, '#skF_5', C_6, D_22)='#skF_7' | D_22!='#skF_8' | ~m1_subset_1('#skF_3'(A_4, '#skF_5', C_6, D_22), '#skF_6') | ~m1_subset_1('#skF_1'(A_4, '#skF_5', C_6, D_22), '#skF_4') | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, '#skF_5', C_6)) | k1_xboole_0=C_6 | k1_xboole_0='#skF_5' | k1_xboole_0=A_4)), inference(resolution, [status(thm)], [c_8, c_282])).
% 2.70/1.43  tff(c_291, plain, (![A_159, C_160, D_161]: ('#skF_3'(A_159, '#skF_5', C_160, D_161)='#skF_7' | D_161!='#skF_8' | ~m1_subset_1('#skF_3'(A_159, '#skF_5', C_160, D_161), '#skF_6') | ~m1_subset_1('#skF_1'(A_159, '#skF_5', C_160, D_161), '#skF_4') | ~m1_subset_1(D_161, k3_zfmisc_1(A_159, '#skF_5', C_160)) | k1_xboole_0=C_160 | k1_xboole_0=A_159)), inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_286])).
% 2.70/1.43  tff(c_295, plain, (![A_4, D_22]: ('#skF_3'(A_4, '#skF_5', '#skF_6', D_22)='#skF_7' | D_22!='#skF_8' | ~m1_subset_1('#skF_1'(A_4, '#skF_5', '#skF_6', D_22), '#skF_4') | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0=A_4)), inference(resolution, [status(thm)], [c_6, c_291])).
% 2.70/1.43  tff(c_300, plain, (![A_162, D_163]: ('#skF_3'(A_162, '#skF_5', '#skF_6', D_163)='#skF_7' | D_163!='#skF_8' | ~m1_subset_1('#skF_1'(A_162, '#skF_5', '#skF_6', D_163), '#skF_4') | ~m1_subset_1(D_163, k3_zfmisc_1(A_162, '#skF_5', '#skF_6')) | k1_xboole_0=A_162)), inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_26, c_295])).
% 2.70/1.43  tff(c_304, plain, (![D_22]: ('#skF_3'('#skF_4', '#skF_5', '#skF_6', D_22)='#skF_7' | D_22!='#skF_8' | ~m1_subset_1(D_22, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_10, c_300])).
% 2.70/1.43  tff(c_309, plain, (![D_164]: ('#skF_3'('#skF_4', '#skF_5', '#skF_6', D_164)='#skF_7' | D_164!='#skF_8' | ~m1_subset_1(D_164, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_30, c_304])).
% 2.70/1.43  tff(c_328, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_34, c_309])).
% 2.70/1.43  tff(c_4, plain, (![A_4, B_5, C_6, D_22]: (k3_mcart_1('#skF_1'(A_4, B_5, C_6, D_22), '#skF_2'(A_4, B_5, C_6, D_22), '#skF_3'(A_4, B_5, C_6, D_22))=D_22 | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, B_5, C_6)) | k1_xboole_0=C_6 | k1_xboole_0=B_5 | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.70/1.43  tff(c_335, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_328, c_4])).
% 2.70/1.43  tff(c_346, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7')='#skF_8' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_335])).
% 2.70/1.43  tff(c_347, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_346])).
% 2.70/1.43  tff(c_18, plain, (![G_48, E_46, A_39, C_41, B_40, F_47]: (k7_mcart_1(A_39, B_40, C_41, k3_mcart_1(E_46, F_47, G_48))=G_48 | k1_xboole_0=C_41 | k1_xboole_0=B_40 | k1_xboole_0=A_39 | ~m1_subset_1(k3_mcart_1(E_46, F_47, G_48), k3_zfmisc_1(A_39, B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.70/1.43  tff(c_389, plain, (![A_39, B_40, C_41]: (k7_mcart_1(A_39, B_40, C_41, k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7'))='#skF_7' | k1_xboole_0=C_41 | k1_xboole_0=B_40 | k1_xboole_0=A_39 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_39, B_40, C_41)))), inference(superposition, [status(thm), theory('equality')], [c_347, c_18])).
% 2.70/1.43  tff(c_405, plain, (![A_171, B_172, C_173]: (k7_mcart_1(A_171, B_172, C_173, '#skF_8')='#skF_7' | k1_xboole_0=C_173 | k1_xboole_0=B_172 | k1_xboole_0=A_171 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_171, B_172, C_173)))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_389])).
% 2.70/1.43  tff(c_411, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_405])).
% 2.70/1.43  tff(c_413, plain, (k2_mcart_1('#skF_8')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_411])).
% 2.70/1.43  tff(c_415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_81, c_413])).
% 2.70/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.43  
% 2.70/1.43  Inference rules
% 2.70/1.43  ----------------------
% 2.70/1.43  #Ref     : 0
% 2.70/1.43  #Sup     : 83
% 2.70/1.43  #Fact    : 0
% 2.70/1.43  #Define  : 0
% 2.70/1.43  #Split   : 0
% 2.70/1.43  #Chain   : 0
% 2.70/1.43  #Close   : 0
% 2.70/1.43  
% 2.70/1.43  Ordering : KBO
% 2.70/1.43  
% 2.70/1.43  Simplification rules
% 2.70/1.43  ----------------------
% 2.70/1.43  #Subsume      : 6
% 2.70/1.43  #Demod        : 40
% 2.70/1.43  #Tautology    : 20
% 2.70/1.43  #SimpNegUnit  : 10
% 2.70/1.43  #BackRed      : 1
% 2.70/1.43  
% 2.70/1.43  #Partial instantiations: 0
% 2.70/1.43  #Strategies tried      : 1
% 2.70/1.43  
% 2.70/1.43  Timing (in seconds)
% 2.70/1.43  ----------------------
% 2.70/1.43  Preprocessing        : 0.33
% 2.70/1.43  Parsing              : 0.17
% 2.70/1.43  CNF conversion       : 0.03
% 2.70/1.43  Main loop            : 0.32
% 2.70/1.43  Inferencing          : 0.13
% 2.70/1.43  Reduction            : 0.09
% 2.70/1.43  Demodulation         : 0.06
% 2.70/1.43  BG Simplification    : 0.03
% 2.70/1.43  Subsumption          : 0.06
% 2.70/1.43  Abstraction          : 0.03
% 2.70/1.43  MUC search           : 0.00
% 2.70/1.43  Cooper               : 0.00
% 2.70/1.43  Total                : 0.69
% 2.70/1.43  Index Insertion      : 0.00
% 2.70/1.43  Index Deletion       : 0.00
% 2.70/1.43  Index Matching       : 0.00
% 2.70/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
