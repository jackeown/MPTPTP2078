%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:48 EST 2020

% Result     : Theorem 15.88s
% Output     : CNFRefutation 16.05s
% Verified   : 
% Statistics : Number of formulae       :  195 (13322 expanded)
%              Number of leaves         :   26 (4719 expanded)
%              Depth                    :   57
%              Number of atoms          :  793 (70348 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( r1_tarski(C,D)
                     => r1_tarski(k3_orders_2(A,C,B),k3_orders_2(A,D,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_orders_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_22,plain,(
    ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k3_orders_2(A_14,B_15,C_16),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_orders_2(A_14)
      | ~ v5_orders_2(A_14)
      | ~ v4_orders_2(A_14)
      | ~ v3_orders_2(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_124,plain,(
    ! [A_73,B_74,C_75] :
      ( m1_subset_1(k3_orders_2(A_73,B_74,C_75),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(C_75,u1_struct_0(A_73))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_131,plain,(
    ! [A_73,B_74,C_75] :
      ( r1_tarski(k3_orders_2(A_73,B_74,C_75),u1_struct_0(A_73))
      | ~ m1_subset_1(C_75,u1_struct_0(A_73))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_124,c_10])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_5,B_6,C_10] :
      ( m1_subset_1('#skF_1'(A_5,B_6,C_10),A_5)
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_5,B_6,C_10] :
      ( r2_hidden('#skF_1'(A_5,B_6,C_10),B_6)
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_216,plain,(
    ! [B_97,D_98,A_99,C_100] :
      ( r2_hidden(B_97,D_98)
      | ~ r2_hidden(B_97,k3_orders_2(A_99,D_98,C_100))
      | ~ m1_subset_1(D_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(C_100,u1_struct_0(A_99))
      | ~ m1_subset_1(B_97,u1_struct_0(A_99))
      | ~ l1_orders_2(A_99)
      | ~ v5_orders_2(A_99)
      | ~ v4_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_909,plain,(
    ! [D_242,A_241,A_239,C_243,C_240] :
      ( r2_hidden('#skF_1'(A_241,k3_orders_2(A_239,D_242,C_240),C_243),D_242)
      | ~ m1_subset_1(D_242,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ m1_subset_1(C_240,u1_struct_0(A_239))
      | ~ m1_subset_1('#skF_1'(A_241,k3_orders_2(A_239,D_242,C_240),C_243),u1_struct_0(A_239))
      | ~ l1_orders_2(A_239)
      | ~ v5_orders_2(A_239)
      | ~ v4_orders_2(A_239)
      | ~ v3_orders_2(A_239)
      | v2_struct_0(A_239)
      | r1_tarski(k3_orders_2(A_239,D_242,C_240),C_243)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(A_241))
      | ~ m1_subset_1(k3_orders_2(A_239,D_242,C_240),k1_zfmisc_1(A_241)) ) ),
    inference(resolution,[status(thm)],[c_6,c_216])).

tff(c_1532,plain,(
    ! [A_415,D_416,C_417,C_418] :
      ( r2_hidden('#skF_1'(u1_struct_0(A_415),k3_orders_2(A_415,D_416,C_417),C_418),D_416)
      | ~ m1_subset_1(D_416,k1_zfmisc_1(u1_struct_0(A_415)))
      | ~ m1_subset_1(C_417,u1_struct_0(A_415))
      | ~ l1_orders_2(A_415)
      | ~ v5_orders_2(A_415)
      | ~ v4_orders_2(A_415)
      | ~ v3_orders_2(A_415)
      | v2_struct_0(A_415)
      | r1_tarski(k3_orders_2(A_415,D_416,C_417),C_418)
      | ~ m1_subset_1(C_418,k1_zfmisc_1(u1_struct_0(A_415)))
      | ~ m1_subset_1(k3_orders_2(A_415,D_416,C_417),k1_zfmisc_1(u1_struct_0(A_415))) ) ),
    inference(resolution,[status(thm)],[c_8,c_909])).

tff(c_4,plain,(
    ! [A_5,B_6,C_10] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6,C_10),C_10)
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1783,plain,(
    ! [C_489,A_490,D_491] :
      ( ~ m1_subset_1(C_489,u1_struct_0(A_490))
      | ~ l1_orders_2(A_490)
      | ~ v5_orders_2(A_490)
      | ~ v4_orders_2(A_490)
      | ~ v3_orders_2(A_490)
      | v2_struct_0(A_490)
      | r1_tarski(k3_orders_2(A_490,D_491,C_489),D_491)
      | ~ m1_subset_1(D_491,k1_zfmisc_1(u1_struct_0(A_490)))
      | ~ m1_subset_1(k3_orders_2(A_490,D_491,C_489),k1_zfmisc_1(u1_struct_0(A_490))) ) ),
    inference(resolution,[status(thm)],[c_1532,c_4])).

tff(c_1791,plain,(
    ! [A_492,B_493,C_494] :
      ( r1_tarski(k3_orders_2(A_492,B_493,C_494),B_493)
      | ~ m1_subset_1(C_494,u1_struct_0(A_492))
      | ~ m1_subset_1(B_493,k1_zfmisc_1(u1_struct_0(A_492)))
      | ~ l1_orders_2(A_492)
      | ~ v5_orders_2(A_492)
      | ~ v4_orders_2(A_492)
      | ~ v3_orders_2(A_492)
      | v2_struct_0(A_492) ) ),
    inference(resolution,[status(thm)],[c_14,c_1783])).

tff(c_1806,plain,(
    ! [A_492,A_12,C_494] :
      ( r1_tarski(k3_orders_2(A_492,A_12,C_494),A_12)
      | ~ m1_subset_1(C_494,u1_struct_0(A_492))
      | ~ l1_orders_2(A_492)
      | ~ v5_orders_2(A_492)
      | ~ v4_orders_2(A_492)
      | ~ v3_orders_2(A_492)
      | v2_struct_0(A_492)
      | ~ r1_tarski(A_12,u1_struct_0(A_492)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1791])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_57,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden('#skF_1'(A_53,B_54,C_55),B_54)
      | r1_tarski(B_54,C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_66,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(B_56,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_57,c_4])).

tff(c_74,plain,(
    r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_66])).

tff(c_41,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_48,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_41])).

tff(c_1803,plain,(
    ! [C_494] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_4',C_494),'#skF_4')
      | ~ m1_subset_1(C_494,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_1791])).

tff(c_1813,plain,(
    ! [C_494] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_4',C_494),'#skF_4')
      | ~ m1_subset_1(C_494,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_1803])).

tff(c_1837,plain,(
    ! [C_496] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_4',C_496),'#skF_4')
      | ~ m1_subset_1(C_496,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1813])).

tff(c_24,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_111,plain,(
    ! [A_66,B_67,C_68,A_69] :
      ( r2_hidden('#skF_1'(A_66,B_67,C_68),A_69)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_69))
      | r1_tarski(B_67,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(resolution,[status(thm)],[c_57,c_2])).

tff(c_132,plain,(
    ! [A_76,A_77,C_80,B_79,A_78] :
      ( r2_hidden('#skF_1'(A_77,B_79,C_80),A_78)
      | ~ m1_subset_1(A_76,k1_zfmisc_1(A_78))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_76))
      | r1_tarski(B_79,C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_77)) ) ),
    inference(resolution,[status(thm)],[c_111,c_2])).

tff(c_226,plain,(
    ! [B_107,B_103,A_105,A_104,C_106] :
      ( r2_hidden('#skF_1'(A_104,B_107,C_106),B_103)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_105))
      | r1_tarski(B_107,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_104))
      | ~ r1_tarski(A_105,B_103) ) ),
    inference(resolution,[status(thm)],[c_12,c_132])).

tff(c_349,plain,(
    ! [A_134,C_136,A_133,B_132,B_135] :
      ( r2_hidden('#skF_1'(A_134,A_133,C_136),B_135)
      | r1_tarski(A_133,C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(A_134))
      | ~ m1_subset_1(A_133,k1_zfmisc_1(A_134))
      | ~ r1_tarski(B_132,B_135)
      | ~ r1_tarski(A_133,B_132) ) ),
    inference(resolution,[status(thm)],[c_12,c_226])).

tff(c_380,plain,(
    ! [A_140,A_141,C_142] :
      ( r2_hidden('#skF_1'(A_140,A_141,C_142),'#skF_5')
      | r1_tarski(A_141,C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(A_140))
      | ~ m1_subset_1(A_141,k1_zfmisc_1(A_140))
      | ~ r1_tarski(A_141,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_349])).

tff(c_792,plain,(
    ! [A_217,A_218,C_219,A_220] :
      ( r2_hidden('#skF_1'(A_217,A_218,C_219),A_220)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_220))
      | r1_tarski(A_218,C_219)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(A_217))
      | ~ m1_subset_1(A_218,k1_zfmisc_1(A_217))
      | ~ r1_tarski(A_218,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_380,c_2])).

tff(c_809,plain,(
    ! [A_221,A_222,A_223] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_221))
      | r1_tarski(A_222,A_221)
      | ~ m1_subset_1(A_221,k1_zfmisc_1(A_223))
      | ~ m1_subset_1(A_222,k1_zfmisc_1(A_223))
      | ~ r1_tarski(A_222,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_792,c_4])).

tff(c_829,plain,(
    ! [A_227,B_228,A_229] :
      ( r1_tarski(A_227,B_228)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(A_229))
      | ~ m1_subset_1(A_227,k1_zfmisc_1(A_229))
      | ~ r1_tarski(A_227,'#skF_4')
      | ~ r1_tarski('#skF_5',B_228) ) ),
    inference(resolution,[status(thm)],[c_12,c_809])).

tff(c_848,plain,(
    ! [A_230,A_231,B_232] :
      ( r1_tarski(A_230,A_231)
      | ~ m1_subset_1(A_230,k1_zfmisc_1(B_232))
      | ~ r1_tarski(A_230,'#skF_4')
      | ~ r1_tarski('#skF_5',A_231)
      | ~ r1_tarski(A_231,B_232) ) ),
    inference(resolution,[status(thm)],[c_12,c_829])).

tff(c_862,plain,(
    ! [A_12,A_231,B_13] :
      ( r1_tarski(A_12,A_231)
      | ~ r1_tarski(A_12,'#skF_4')
      | ~ r1_tarski('#skF_5',A_231)
      | ~ r1_tarski(A_231,B_13)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_848])).

tff(c_1962,plain,(
    ! [C_502,A_503,B_504] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_4',C_502),A_503)
      | ~ r1_tarski('#skF_5',A_503)
      | ~ r1_tarski(A_503,B_504)
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_4',C_502),B_504)
      | ~ m1_subset_1(C_502,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1837,c_862])).

tff(c_2002,plain,(
    ! [C_502] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_4',C_502),'#skF_5')
      | ~ r1_tarski('#skF_5','#skF_5')
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_4',C_502),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_502,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_1962])).

tff(c_2030,plain,(
    ! [C_505] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_4',C_505),'#skF_5')
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_4',C_505),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_505,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2002])).

tff(c_2034,plain,(
    ! [C_75] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_4',C_75),'#skF_5')
      | ~ m1_subset_1(C_75,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_131,c_2030])).

tff(c_2037,plain,(
    ! [C_75] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_4',C_75),'#skF_5')
      | ~ m1_subset_1(C_75,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_2034])).

tff(c_2038,plain,(
    ! [C_75] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_4',C_75),'#skF_5')
      | ~ m1_subset_1(C_75,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2037])).

tff(c_1801,plain,(
    ! [C_494] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',C_494),'#skF_5')
      | ~ m1_subset_1(C_494,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_1791])).

tff(c_1809,plain,(
    ! [C_494] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',C_494),'#skF_5')
      | ~ m1_subset_1(C_494,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_1801])).

tff(c_1810,plain,(
    ! [C_494] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',C_494),'#skF_5')
      | ~ m1_subset_1(C_494,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1809])).

tff(c_75,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_371,plain,(
    ! [A_137,A_138,C_139] :
      ( r2_hidden('#skF_1'(A_137,A_138,C_139),'#skF_4')
      | r1_tarski(A_138,C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(A_137))
      | ~ m1_subset_1(A_138,k1_zfmisc_1(A_137))
      | ~ r1_tarski(A_138,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_75,c_349])).

tff(c_696,plain,(
    ! [A_193,A_194,C_195,A_196] :
      ( r2_hidden('#skF_1'(A_193,A_194,C_195),A_196)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_196))
      | r1_tarski(A_194,C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(A_193))
      | ~ m1_subset_1(A_194,k1_zfmisc_1(A_193))
      | ~ r1_tarski(A_194,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_371,c_2])).

tff(c_720,plain,(
    ! [A_200,A_201,A_202] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_200))
      | r1_tarski(A_201,A_200)
      | ~ m1_subset_1(A_200,k1_zfmisc_1(A_202))
      | ~ m1_subset_1(A_201,k1_zfmisc_1(A_202))
      | ~ r1_tarski(A_201,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_696,c_4])).

tff(c_728,plain,(
    ! [A_203,B_204,A_205] :
      ( r1_tarski(A_203,B_204)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(A_205))
      | ~ m1_subset_1(A_203,k1_zfmisc_1(A_205))
      | ~ r1_tarski(A_203,'#skF_4')
      | ~ r1_tarski('#skF_4',B_204) ) ),
    inference(resolution,[status(thm)],[c_12,c_720])).

tff(c_749,plain,(
    ! [A_206,A_207,B_208] :
      ( r1_tarski(A_206,A_207)
      | ~ m1_subset_1(A_206,k1_zfmisc_1(B_208))
      | ~ r1_tarski(A_206,'#skF_4')
      | ~ r1_tarski('#skF_4',A_207)
      | ~ r1_tarski(A_207,B_208) ) ),
    inference(resolution,[status(thm)],[c_12,c_728])).

tff(c_763,plain,(
    ! [A_12,A_207,B_13] :
      ( r1_tarski(A_12,A_207)
      | ~ r1_tarski(A_12,'#skF_4')
      | ~ r1_tarski('#skF_4',A_207)
      | ~ r1_tarski(A_207,B_13)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_749])).

tff(c_2075,plain,(
    ! [C_510,A_511,B_512] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_4',C_510),A_511)
      | ~ r1_tarski('#skF_4',A_511)
      | ~ r1_tarski(A_511,B_512)
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_4',C_510),B_512)
      | ~ m1_subset_1(C_510,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1837,c_763])).

tff(c_2460,plain,(
    ! [C_544,C_545] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_4',C_544),k3_orders_2('#skF_2','#skF_5',C_545))
      | ~ r1_tarski('#skF_4',k3_orders_2('#skF_2','#skF_5',C_545))
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_4',C_544),'#skF_5')
      | ~ m1_subset_1(C_544,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_545,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1810,c_2075])).

tff(c_2485,plain,
    ( ~ r1_tarski('#skF_4',k3_orders_2('#skF_2','#skF_5','#skF_3'))
    | ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2460,c_22])).

tff(c_2499,plain,
    ( ~ r1_tarski('#skF_4',k3_orders_2('#skF_2','#skF_5','#skF_3'))
    | ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2485])).

tff(c_2509,plain,(
    ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2499])).

tff(c_2512,plain,(
    ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2038,c_2509])).

tff(c_2519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2512])).

tff(c_2521,plain,(
    r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_2499])).

tff(c_240,plain,(
    ! [B_103,A_104,C_106,A_12,B_13] :
      ( r2_hidden('#skF_1'(A_104,A_12,C_106),B_103)
      | r1_tarski(A_12,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(A_12,k1_zfmisc_1(A_104))
      | ~ r1_tarski(B_13,B_103)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_226])).

tff(c_3036,plain,(
    ! [A_572,A_573,C_574] :
      ( r2_hidden('#skF_1'(A_572,A_573,C_574),'#skF_5')
      | r1_tarski(A_573,C_574)
      | ~ m1_subset_1(C_574,k1_zfmisc_1(A_572))
      | ~ m1_subset_1(A_573,k1_zfmisc_1(A_572))
      | ~ r1_tarski(A_573,k3_orders_2('#skF_2','#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2521,c_240])).

tff(c_3045,plain,(
    ! [A_575,A_576] :
      ( r1_tarski(A_575,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_576))
      | ~ m1_subset_1(A_575,k1_zfmisc_1(A_576))
      | ~ r1_tarski(A_575,k3_orders_2('#skF_2','#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3036,c_4])).

tff(c_3053,plain,(
    ! [A_577] :
      ( r1_tarski(A_577,'#skF_5')
      | ~ m1_subset_1(A_577,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_577,k3_orders_2('#skF_2','#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_26,c_3045])).

tff(c_3057,plain,(
    ! [B_15,C_16] :
      ( r1_tarski(k3_orders_2('#skF_2',B_15,C_16),'#skF_5')
      | ~ r1_tarski(k3_orders_2('#skF_2',B_15,C_16),k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | ~ m1_subset_1(C_16,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_3053])).

tff(c_3074,plain,(
    ! [B_15,C_16] :
      ( r1_tarski(k3_orders_2('#skF_2',B_15,C_16),'#skF_5')
      | ~ r1_tarski(k3_orders_2('#skF_2',B_15,C_16),k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | ~ m1_subset_1(C_16,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_3057])).

tff(c_3082,plain,(
    ! [B_578,C_579] :
      ( r1_tarski(k3_orders_2('#skF_2',B_578,C_579),'#skF_5')
      | ~ r1_tarski(k3_orders_2('#skF_2',B_578,C_579),k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | ~ m1_subset_1(C_579,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_578,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3074])).

tff(c_3101,plain,(
    ! [C_494] :
      ( r1_tarski(k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),C_494),'#skF_5')
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_494,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1806,c_3082])).

tff(c_3125,plain,(
    ! [C_494] :
      ( r1_tarski(k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),C_494),'#skF_5')
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_494,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_3101])).

tff(c_3126,plain,(
    ! [C_494] :
      ( r1_tarski(k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),C_494),'#skF_5')
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_494,u1_struct_0('#skF_2'))
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3125])).

tff(c_3264,plain,(
    ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3126])).

tff(c_3267,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_131,c_3264])).

tff(c_3270,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_30,c_3267])).

tff(c_3272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3270])).

tff(c_3273,plain,(
    ! [C_494] :
      ( ~ m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski(k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),C_494),'#skF_5')
      | ~ m1_subset_1(C_494,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_3126])).

tff(c_3326,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3273])).

tff(c_3329,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_3326])).

tff(c_3335,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_30,c_3329])).

tff(c_3337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3335])).

tff(c_3339,plain,(
    m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3273])).

tff(c_73,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_66])).

tff(c_2557,plain,(
    r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2521,c_73])).

tff(c_1789,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_tarski(k3_orders_2(A_14,B_15,C_16),B_15)
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_orders_2(A_14)
      | ~ v5_orders_2(A_14)
      | ~ v4_orders_2(A_14)
      | ~ v3_orders_2(A_14)
      | v2_struct_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_1783])).

tff(c_3348,plain,(
    ! [C_16] :
      ( r1_tarski(k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),C_16),k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | ~ m1_subset_1(C_16,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3339,c_1789])).

tff(c_3436,plain,(
    ! [C_16] :
      ( r1_tarski(k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),C_16),k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | ~ m1_subset_1(C_16,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_3348])).

tff(c_3437,plain,(
    ! [C_16] :
      ( r1_tarski(k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),C_16),k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | ~ m1_subset_1(C_16,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3436])).

tff(c_3274,plain,(
    r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3126])).

tff(c_5391,plain,(
    ! [A_679,A_680,C_681] :
      ( r2_hidden('#skF_1'(A_679,A_680,C_681),k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | r1_tarski(A_680,C_681)
      | ~ m1_subset_1(C_681,k1_zfmisc_1(A_679))
      | ~ m1_subset_1(A_680,k1_zfmisc_1(A_679))
      | ~ r1_tarski(A_680,k3_orders_2('#skF_2','#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2557,c_240])).

tff(c_20,plain,(
    ! [A_17,B_25,C_29,D_31] :
      ( r2_orders_2(A_17,B_25,C_29)
      | ~ r2_hidden(B_25,k3_orders_2(A_17,D_31,C_29))
      | ~ m1_subset_1(D_31,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(C_29,u1_struct_0(A_17))
      | ~ m1_subset_1(B_25,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | ~ v5_orders_2(A_17)
      | ~ v4_orders_2(A_17)
      | ~ v3_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5401,plain,(
    ! [A_679,A_680,C_681] :
      ( r2_orders_2('#skF_2','#skF_1'(A_679,A_680,C_681),'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_679,A_680,C_681),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(A_680,C_681)
      | ~ m1_subset_1(C_681,k1_zfmisc_1(A_679))
      | ~ m1_subset_1(A_680,k1_zfmisc_1(A_679))
      | ~ r1_tarski(A_680,k3_orders_2('#skF_2','#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5391,c_20])).

tff(c_5418,plain,(
    ! [A_679,A_680,C_681] :
      ( r2_orders_2('#skF_2','#skF_1'(A_679,A_680,C_681),'#skF_3')
      | ~ m1_subset_1('#skF_1'(A_679,A_680,C_681),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_tarski(A_680,C_681)
      | ~ m1_subset_1(C_681,k1_zfmisc_1(A_679))
      | ~ m1_subset_1(A_680,k1_zfmisc_1(A_679))
      | ~ r1_tarski(A_680,k3_orders_2('#skF_2','#skF_4','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_5401])).

tff(c_6962,plain,(
    ! [A_788,A_789,C_790] :
      ( r2_orders_2('#skF_2','#skF_1'(A_788,A_789,C_790),'#skF_3')
      | ~ m1_subset_1('#skF_1'(A_788,A_789,C_790),u1_struct_0('#skF_2'))
      | r1_tarski(A_789,C_790)
      | ~ m1_subset_1(C_790,k1_zfmisc_1(A_788))
      | ~ m1_subset_1(A_789,k1_zfmisc_1(A_788))
      | ~ r1_tarski(A_789,k3_orders_2('#skF_2','#skF_4','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_5418])).

tff(c_6967,plain,(
    ! [B_6,C_10] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_6,C_10),'#skF_3')
      | ~ r1_tarski(B_6,k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_6962])).

tff(c_397,plain,(
    ! [B_145,A_146,D_147,C_148] :
      ( r2_hidden(B_145,k3_orders_2(A_146,D_147,C_148))
      | ~ r2_hidden(B_145,D_147)
      | ~ r2_orders_2(A_146,B_145,C_148)
      | ~ m1_subset_1(D_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ m1_subset_1(C_148,u1_struct_0(A_146))
      | ~ m1_subset_1(B_145,u1_struct_0(A_146))
      | ~ l1_orders_2(A_146)
      | ~ v5_orders_2(A_146)
      | ~ v4_orders_2(A_146)
      | ~ v3_orders_2(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_674,plain,(
    ! [B_187,A_188,A_189,C_190] :
      ( r2_hidden(B_187,k3_orders_2(A_188,A_189,C_190))
      | ~ r2_hidden(B_187,A_189)
      | ~ r2_orders_2(A_188,B_187,C_190)
      | ~ m1_subset_1(C_190,u1_struct_0(A_188))
      | ~ m1_subset_1(B_187,u1_struct_0(A_188))
      | ~ l1_orders_2(A_188)
      | ~ v5_orders_2(A_188)
      | ~ v4_orders_2(A_188)
      | ~ v3_orders_2(A_188)
      | v2_struct_0(A_188)
      | ~ r1_tarski(A_189,u1_struct_0(A_188)) ) ),
    inference(resolution,[status(thm)],[c_12,c_397])).

tff(c_3505,plain,(
    ! [A_592,C_595,A_594,B_591,A_593] :
      ( r1_tarski(B_591,k3_orders_2(A_593,A_594,C_595))
      | ~ m1_subset_1(k3_orders_2(A_593,A_594,C_595),k1_zfmisc_1(A_592))
      | ~ m1_subset_1(B_591,k1_zfmisc_1(A_592))
      | ~ r2_hidden('#skF_1'(A_592,B_591,k3_orders_2(A_593,A_594,C_595)),A_594)
      | ~ r2_orders_2(A_593,'#skF_1'(A_592,B_591,k3_orders_2(A_593,A_594,C_595)),C_595)
      | ~ m1_subset_1(C_595,u1_struct_0(A_593))
      | ~ m1_subset_1('#skF_1'(A_592,B_591,k3_orders_2(A_593,A_594,C_595)),u1_struct_0(A_593))
      | ~ l1_orders_2(A_593)
      | ~ v5_orders_2(A_593)
      | ~ v4_orders_2(A_593)
      | ~ v3_orders_2(A_593)
      | v2_struct_0(A_593)
      | ~ r1_tarski(A_594,u1_struct_0(A_593)) ) ),
    inference(resolution,[status(thm)],[c_674,c_4])).

tff(c_7854,plain,(
    ! [A_823,A_824,B_825,C_826] :
      ( ~ r2_orders_2(A_823,'#skF_1'(A_824,B_825,k3_orders_2(A_823,B_825,C_826)),C_826)
      | ~ m1_subset_1(C_826,u1_struct_0(A_823))
      | ~ m1_subset_1('#skF_1'(A_824,B_825,k3_orders_2(A_823,B_825,C_826)),u1_struct_0(A_823))
      | ~ l1_orders_2(A_823)
      | ~ v5_orders_2(A_823)
      | ~ v4_orders_2(A_823)
      | ~ v3_orders_2(A_823)
      | v2_struct_0(A_823)
      | ~ r1_tarski(B_825,u1_struct_0(A_823))
      | r1_tarski(B_825,k3_orders_2(A_823,B_825,C_826))
      | ~ m1_subset_1(k3_orders_2(A_823,B_825,C_826),k1_zfmisc_1(A_824))
      | ~ m1_subset_1(B_825,k1_zfmisc_1(A_824)) ) ),
    inference(resolution,[status(thm)],[c_6,c_3505])).

tff(c_7857,plain,(
    ! [B_6] :
      ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_6,k3_orders_2('#skF_2',B_6,'#skF_3')),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(B_6,u1_struct_0('#skF_2'))
      | ~ r1_tarski(B_6,k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | r1_tarski(B_6,k3_orders_2('#skF_2',B_6,'#skF_3'))
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_6,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_6967,c_7854])).

tff(c_7863,plain,(
    ! [B_6] :
      ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_6,k3_orders_2('#skF_2',B_6,'#skF_3')),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(B_6,u1_struct_0('#skF_2'))
      | ~ r1_tarski(B_6,k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | r1_tarski(B_6,k3_orders_2('#skF_2',B_6,'#skF_3'))
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_6,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_7857])).

tff(c_14353,plain,(
    ! [B_1158] :
      ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_1158,k3_orders_2('#skF_2',B_1158,'#skF_3')),u1_struct_0('#skF_2'))
      | ~ r1_tarski(B_1158,u1_struct_0('#skF_2'))
      | ~ r1_tarski(B_1158,k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | r1_tarski(B_1158,k3_orders_2('#skF_2',B_1158,'#skF_3'))
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_1158,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1158,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_7863])).

tff(c_14851,plain,(
    ! [B_1183] :
      ( ~ r1_tarski(B_1183,u1_struct_0('#skF_2'))
      | ~ r1_tarski(B_1183,k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | r1_tarski(B_1183,k3_orders_2('#skF_2',B_1183,'#skF_3'))
      | ~ m1_subset_1(k3_orders_2('#skF_2',B_1183,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1183,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_14353])).

tff(c_14856,plain,(
    ! [B_15] :
      ( ~ r1_tarski(B_15,u1_struct_0('#skF_2'))
      | ~ r1_tarski(B_15,k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | r1_tarski(B_15,k3_orders_2('#skF_2',B_15,'#skF_3'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_14851])).

tff(c_14866,plain,(
    ! [B_15] :
      ( ~ r1_tarski(B_15,u1_struct_0('#skF_2'))
      | ~ r1_tarski(B_15,k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | r1_tarski(B_15,k3_orders_2('#skF_2',B_15,'#skF_3'))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_14856])).

tff(c_14869,plain,(
    ! [B_1184] :
      ( ~ r1_tarski(B_1184,u1_struct_0('#skF_2'))
      | ~ r1_tarski(B_1184,k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | r1_tarski(B_1184,k3_orders_2('#skF_2',B_1184,'#skF_3'))
      | ~ m1_subset_1(B_1184,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_14866])).

tff(c_14871,plain,
    ( ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
    | ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_4','#skF_3'))
    | r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_3339,c_14869])).

tff(c_14887,plain,(
    r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_3274,c_14871])).

tff(c_15191,plain,(
    ! [A_1192,A_1193,C_1194] :
      ( r2_hidden('#skF_1'(A_1192,A_1193,C_1194),k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_3'))
      | r1_tarski(A_1193,C_1194)
      | ~ m1_subset_1(C_1194,k1_zfmisc_1(A_1192))
      | ~ m1_subset_1(A_1193,k1_zfmisc_1(A_1192))
      | ~ r1_tarski(A_1193,k3_orders_2('#skF_2','#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14887,c_240])).

tff(c_15232,plain,(
    ! [A_1195,A_1196] :
      ( r1_tarski(A_1195,k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_3'))
      | ~ m1_subset_1(k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_3'),k1_zfmisc_1(A_1196))
      | ~ m1_subset_1(A_1195,k1_zfmisc_1(A_1196))
      | ~ r1_tarski(A_1195,k3_orders_2('#skF_2','#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_15191,c_4])).

tff(c_15653,plain,(
    ! [A_1209,B_1210] :
      ( r1_tarski(A_1209,k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_3'))
      | ~ m1_subset_1(A_1209,k1_zfmisc_1(B_1210))
      | ~ r1_tarski(A_1209,k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | ~ r1_tarski(k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_3'),B_1210) ) ),
    inference(resolution,[status(thm)],[c_12,c_15232])).

tff(c_15675,plain,(
    ! [A_1211,B_1212] :
      ( r1_tarski(A_1211,k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_3'))
      | ~ r1_tarski(A_1211,k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | ~ r1_tarski(k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_3'),B_1212)
      | ~ r1_tarski(A_1211,B_1212) ) ),
    inference(resolution,[status(thm)],[c_12,c_15653])).

tff(c_15690,plain,(
    ! [A_1211] :
      ( r1_tarski(A_1211,k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_3'))
      | ~ r1_tarski(A_1211,k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3437,c_15675])).

tff(c_15750,plain,(
    ! [A_1213] :
      ( r1_tarski(A_1213,k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_3'))
      | ~ r1_tarski(A_1213,k3_orders_2('#skF_2','#skF_4','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_15690])).

tff(c_17718,plain,(
    ! [A_1258,A_1259,C_1260,A_1261] :
      ( r2_hidden('#skF_1'(A_1258,A_1259,C_1260),k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_3'))
      | r1_tarski(A_1259,C_1260)
      | ~ m1_subset_1(C_1260,k1_zfmisc_1(A_1258))
      | ~ m1_subset_1(A_1259,k1_zfmisc_1(A_1258))
      | ~ r1_tarski(A_1259,A_1261)
      | ~ r1_tarski(A_1261,k3_orders_2('#skF_2','#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_15750,c_240])).

tff(c_17810,plain,(
    ! [A_1258,C_1260] :
      ( r2_hidden('#skF_1'(A_1258,k3_orders_2('#skF_2','#skF_4','#skF_3'),C_1260),k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_3'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),C_1260)
      | ~ m1_subset_1(C_1260,k1_zfmisc_1(A_1258))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(A_1258))
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2557,c_17718])).

tff(c_18036,plain,(
    ! [A_1264,C_1265] :
      ( r2_hidden('#skF_1'(A_1264,k3_orders_2('#skF_2','#skF_4','#skF_3'),C_1265),k3_orders_2('#skF_2',k3_orders_2('#skF_2','#skF_4','#skF_3'),'#skF_3'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),C_1265)
      | ~ m1_subset_1(C_1265,k1_zfmisc_1(A_1264))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(A_1264)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_17810])).

tff(c_18048,plain,(
    ! [A_1264,C_1265] :
      ( r2_orders_2('#skF_2','#skF_1'(A_1264,k3_orders_2('#skF_2','#skF_4','#skF_3'),C_1265),'#skF_3')
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_1264,k3_orders_2('#skF_2','#skF_4','#skF_3'),C_1265),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),C_1265)
      | ~ m1_subset_1(C_1265,k1_zfmisc_1(A_1264))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(A_1264)) ) ),
    inference(resolution,[status(thm)],[c_18036,c_20])).

tff(c_18069,plain,(
    ! [A_1264,C_1265] :
      ( r2_orders_2('#skF_2','#skF_1'(A_1264,k3_orders_2('#skF_2','#skF_4','#skF_3'),C_1265),'#skF_3')
      | ~ m1_subset_1('#skF_1'(A_1264,k3_orders_2('#skF_2','#skF_4','#skF_3'),C_1265),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),C_1265)
      | ~ m1_subset_1(C_1265,k1_zfmisc_1(A_1264))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(A_1264)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_3339,c_18048])).

tff(c_18849,plain,(
    ! [A_1305,C_1306] :
      ( r2_orders_2('#skF_2','#skF_1'(A_1305,k3_orders_2('#skF_2','#skF_4','#skF_3'),C_1306),'#skF_3')
      | ~ m1_subset_1('#skF_1'(A_1305,k3_orders_2('#skF_2','#skF_4','#skF_3'),C_1306),u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),C_1306)
      | ~ m1_subset_1(C_1306,k1_zfmisc_1(A_1305))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(A_1305)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_18069])).

tff(c_18853,plain,(
    ! [C_10] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_4','#skF_3'),C_10),'#skF_3')
      | r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_18849])).

tff(c_18857,plain,(
    ! [C_1307] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_4','#skF_3'),C_1307),'#skF_3')
      | r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),C_1307)
      | ~ m1_subset_1(C_1307,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3339,c_18853])).

tff(c_407,plain,(
    ! [B_145,C_148] :
      ( r2_hidden(B_145,k3_orders_2('#skF_2','#skF_5',C_148))
      | ~ r2_hidden(B_145,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_145,C_148)
      | ~ m1_subset_1(C_148,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_397])).

tff(c_415,plain,(
    ! [B_145,C_148] :
      ( r2_hidden(B_145,k3_orders_2('#skF_2','#skF_5',C_148))
      | ~ r2_hidden(B_145,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_145,C_148)
      | ~ m1_subset_1(C_148,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_407])).

tff(c_494,plain,(
    ! [B_153,C_154] :
      ( r2_hidden(B_153,k3_orders_2('#skF_2','#skF_5',C_154))
      | ~ r2_hidden(B_153,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_153,C_154)
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_153,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_415])).

tff(c_513,plain,(
    ! [B_6,C_154,A_5] :
      ( r1_tarski(B_6,k3_orders_2('#skF_2','#skF_5',C_154))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_154),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5))
      | ~ r2_hidden('#skF_1'(A_5,B_6,k3_orders_2('#skF_2','#skF_5',C_154)),'#skF_5')
      | ~ r2_orders_2('#skF_2','#skF_1'(A_5,B_6,k3_orders_2('#skF_2','#skF_5',C_154)),C_154)
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_5,B_6,k3_orders_2('#skF_2','#skF_5',C_154)),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_494,c_4])).

tff(c_18907,plain,
    ( ~ m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3'))
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_18857,c_513])).

tff(c_18979,plain,
    ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5')
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3'))
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3339,c_18907])).

tff(c_18980,plain,
    ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5')
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_18979])).

tff(c_19513,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_18980])).

tff(c_19516,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_19513])).

tff(c_19522,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_26,c_30,c_19516])).

tff(c_19524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_19522])).

tff(c_19526,plain,(
    m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_18980])).

tff(c_64,plain,(
    ! [B_54,A_53] :
      ( r1_tarski(B_54,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(resolution,[status(thm)],[c_57,c_4])).

tff(c_130,plain,(
    ! [A_73,B_74,C_75] :
      ( r1_tarski(k3_orders_2(A_73,B_74,C_75),k3_orders_2(A_73,B_74,C_75))
      | ~ m1_subset_1(C_75,u1_struct_0(A_73))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_124,c_64])).

tff(c_1815,plain,(
    ! [C_495] :
      ( r1_tarski(k3_orders_2('#skF_2','#skF_5',C_495),'#skF_5')
      | ~ m1_subset_1(C_495,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1809])).

tff(c_2343,plain,(
    ! [A_526,A_527,C_528,C_529] :
      ( r2_hidden('#skF_1'(A_526,A_527,C_528),'#skF_5')
      | r1_tarski(A_527,C_528)
      | ~ m1_subset_1(C_528,k1_zfmisc_1(A_526))
      | ~ m1_subset_1(A_527,k1_zfmisc_1(A_526))
      | ~ r1_tarski(A_527,k3_orders_2('#skF_2','#skF_5',C_529))
      | ~ m1_subset_1(C_529,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1815,c_240])).

tff(c_2351,plain,(
    ! [A_526,C_75,C_528] :
      ( r2_hidden('#skF_1'(A_526,k3_orders_2('#skF_2','#skF_5',C_75),C_528),'#skF_5')
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_75),C_528)
      | ~ m1_subset_1(C_528,k1_zfmisc_1(A_526))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_75),k1_zfmisc_1(A_526))
      | ~ m1_subset_1(C_75,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_130,c_2343])).

tff(c_2359,plain,(
    ! [A_526,C_75,C_528] :
      ( r2_hidden('#skF_1'(A_526,k3_orders_2('#skF_2','#skF_5',C_75),C_528),'#skF_5')
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_75),C_528)
      | ~ m1_subset_1(C_528,k1_zfmisc_1(A_526))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_75),k1_zfmisc_1(A_526))
      | ~ m1_subset_1(C_75,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_26,c_2351])).

tff(c_2500,plain,(
    ! [A_546,C_547,C_548] :
      ( r2_hidden('#skF_1'(A_546,k3_orders_2('#skF_2','#skF_5',C_547),C_548),'#skF_5')
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_547),C_548)
      | ~ m1_subset_1(C_548,k1_zfmisc_1(A_546))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_547),k1_zfmisc_1(A_546))
      | ~ m1_subset_1(C_547,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2359])).

tff(c_18211,plain,(
    ! [A_1280,C_1281,C_1282,A_1283] :
      ( r2_hidden('#skF_1'(A_1280,k3_orders_2('#skF_2','#skF_5',C_1281),C_1282),A_1283)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1283))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_1281),C_1282)
      | ~ m1_subset_1(C_1282,k1_zfmisc_1(A_1280))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_1281),k1_zfmisc_1(A_1280))
      | ~ m1_subset_1(C_1281,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_2500,c_2])).

tff(c_18259,plain,(
    ! [A_1284,C_1285,A_1286] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1284))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_1285),A_1284)
      | ~ m1_subset_1(A_1284,k1_zfmisc_1(A_1286))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_1285),k1_zfmisc_1(A_1286))
      | ~ m1_subset_1(C_1285,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_18211,c_4])).

tff(c_18276,plain,(
    ! [A_12,C_1285,B_13] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_12))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_1285),A_12)
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_1285),k1_zfmisc_1(B_13))
      | ~ m1_subset_1(C_1285,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_18259])).

tff(c_19528,plain,(
    ! [A_12] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_12))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),A_12)
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_12,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_19526,c_18276])).

tff(c_20046,plain,(
    ! [A_1328] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1328))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),A_1328)
      | ~ r1_tarski(A_1328,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_19528])).

tff(c_20108,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5'))
    | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_20046])).

tff(c_20109,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_20108])).

tff(c_20112,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_20109])).

tff(c_20116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_20112])).

tff(c_20118,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_20108])).

tff(c_5513,plain,(
    ! [A_693,A_694,C_695,A_696] :
      ( r2_hidden('#skF_1'(A_693,A_694,C_695),A_696)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_696))
      | r1_tarski(A_694,C_695)
      | ~ m1_subset_1(C_695,k1_zfmisc_1(A_693))
      | ~ m1_subset_1(A_694,k1_zfmisc_1(A_693))
      | ~ r1_tarski(A_694,k3_orders_2('#skF_2','#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3036,c_2])).

tff(c_11048,plain,(
    ! [C_967,A_965,A_966,A_963,A_964] :
      ( r2_hidden('#skF_1'(A_965,A_963,C_967),A_966)
      | ~ m1_subset_1(A_964,k1_zfmisc_1(A_966))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_964))
      | r1_tarski(A_963,C_967)
      | ~ m1_subset_1(C_967,k1_zfmisc_1(A_965))
      | ~ m1_subset_1(A_963,k1_zfmisc_1(A_965))
      | ~ r1_tarski(A_963,k3_orders_2('#skF_2','#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5513,c_2])).

tff(c_11065,plain,(
    ! [C_967,A_965,A_12,B_13,A_963] :
      ( r2_hidden('#skF_1'(A_965,A_963,C_967),B_13)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_12))
      | r1_tarski(A_963,C_967)
      | ~ m1_subset_1(C_967,k1_zfmisc_1(A_965))
      | ~ m1_subset_1(A_963,k1_zfmisc_1(A_965))
      | ~ r1_tarski(A_963,k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_11048])).

tff(c_20241,plain,(
    ! [A_965,A_963,C_967,B_13] :
      ( r2_hidden('#skF_1'(A_965,A_963,C_967),B_13)
      | r1_tarski(A_963,C_967)
      | ~ m1_subset_1(C_967,k1_zfmisc_1(A_965))
      | ~ m1_subset_1(A_963,k1_zfmisc_1(A_965))
      | ~ r1_tarski(A_963,k3_orders_2('#skF_2','#skF_4','#skF_3'))
      | ~ r1_tarski('#skF_5',B_13) ) ),
    inference(resolution,[status(thm)],[c_20118,c_11065])).

tff(c_19525,plain,
    ( ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_18980])).

tff(c_27371,plain,(
    ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_19525])).

tff(c_27490,plain,
    ( r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3'))
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_4','#skF_3'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_20241,c_27371])).

tff(c_27562,plain,(
    r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2557,c_3339,c_19526,c_27490])).

tff(c_27564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_27562])).

tff(c_27565,plain,(
    ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_19525])).

tff(c_27581,plain,
    ( r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3'))
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_27565])).

tff(c_27584,plain,(
    r1_tarski(k3_orders_2('#skF_2','#skF_4','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3339,c_19526,c_27581])).

tff(c_27586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_27584])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:32:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.88/9.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.88/9.03  
% 15.88/9.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.88/9.04  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 15.88/9.04  
% 15.88/9.04  %Foreground sorts:
% 15.88/9.04  
% 15.88/9.04  
% 15.88/9.04  %Background operators:
% 15.88/9.04  
% 15.88/9.04  
% 15.88/9.04  %Foreground operators:
% 15.88/9.04  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.88/9.04  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 15.88/9.04  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 15.88/9.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.88/9.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.88/9.04  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 15.88/9.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.88/9.04  tff('#skF_5', type, '#skF_5': $i).
% 15.88/9.04  tff('#skF_2', type, '#skF_2': $i).
% 15.88/9.04  tff('#skF_3', type, '#skF_3': $i).
% 15.88/9.04  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 15.88/9.04  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 15.88/9.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.88/9.04  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 15.88/9.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.88/9.04  tff('#skF_4', type, '#skF_4': $i).
% 15.88/9.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.88/9.04  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 15.88/9.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.88/9.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.88/9.04  
% 16.05/9.07  tff(f_118, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, D) => r1_tarski(k3_orders_2(A, C, B), k3_orders_2(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_orders_2)).
% 16.05/9.07  tff(f_67, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 16.05/9.07  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.05/9.07  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 16.05/9.07  tff(f_93, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 16.05/9.07  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 16.05/9.07  tff(c_22, plain, (~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.05/9.07  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.05/9.07  tff(c_38, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.05/9.07  tff(c_36, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.05/9.07  tff(c_34, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.05/9.07  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.05/9.07  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.05/9.07  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.05/9.07  tff(c_14, plain, (![A_14, B_15, C_16]: (m1_subset_1(k3_orders_2(A_14, B_15, C_16), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(C_16, u1_struct_0(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_orders_2(A_14) | ~v5_orders_2(A_14) | ~v4_orders_2(A_14) | ~v3_orders_2(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.05/9.07  tff(c_124, plain, (![A_73, B_74, C_75]: (m1_subset_1(k3_orders_2(A_73, B_74, C_75), k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(C_75, u1_struct_0(A_73)) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.05/9.07  tff(c_10, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.05/9.07  tff(c_131, plain, (![A_73, B_74, C_75]: (r1_tarski(k3_orders_2(A_73, B_74, C_75), u1_struct_0(A_73)) | ~m1_subset_1(C_75, u1_struct_0(A_73)) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(resolution, [status(thm)], [c_124, c_10])).
% 16.05/9.07  tff(c_12, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.05/9.07  tff(c_8, plain, (![A_5, B_6, C_10]: (m1_subset_1('#skF_1'(A_5, B_6, C_10), A_5) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.05/9.07  tff(c_6, plain, (![A_5, B_6, C_10]: (r2_hidden('#skF_1'(A_5, B_6, C_10), B_6) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.05/9.07  tff(c_216, plain, (![B_97, D_98, A_99, C_100]: (r2_hidden(B_97, D_98) | ~r2_hidden(B_97, k3_orders_2(A_99, D_98, C_100)) | ~m1_subset_1(D_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_subset_1(C_100, u1_struct_0(A_99)) | ~m1_subset_1(B_97, u1_struct_0(A_99)) | ~l1_orders_2(A_99) | ~v5_orders_2(A_99) | ~v4_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.05/9.07  tff(c_909, plain, (![D_242, A_241, A_239, C_243, C_240]: (r2_hidden('#skF_1'(A_241, k3_orders_2(A_239, D_242, C_240), C_243), D_242) | ~m1_subset_1(D_242, k1_zfmisc_1(u1_struct_0(A_239))) | ~m1_subset_1(C_240, u1_struct_0(A_239)) | ~m1_subset_1('#skF_1'(A_241, k3_orders_2(A_239, D_242, C_240), C_243), u1_struct_0(A_239)) | ~l1_orders_2(A_239) | ~v5_orders_2(A_239) | ~v4_orders_2(A_239) | ~v3_orders_2(A_239) | v2_struct_0(A_239) | r1_tarski(k3_orders_2(A_239, D_242, C_240), C_243) | ~m1_subset_1(C_243, k1_zfmisc_1(A_241)) | ~m1_subset_1(k3_orders_2(A_239, D_242, C_240), k1_zfmisc_1(A_241)))), inference(resolution, [status(thm)], [c_6, c_216])).
% 16.05/9.07  tff(c_1532, plain, (![A_415, D_416, C_417, C_418]: (r2_hidden('#skF_1'(u1_struct_0(A_415), k3_orders_2(A_415, D_416, C_417), C_418), D_416) | ~m1_subset_1(D_416, k1_zfmisc_1(u1_struct_0(A_415))) | ~m1_subset_1(C_417, u1_struct_0(A_415)) | ~l1_orders_2(A_415) | ~v5_orders_2(A_415) | ~v4_orders_2(A_415) | ~v3_orders_2(A_415) | v2_struct_0(A_415) | r1_tarski(k3_orders_2(A_415, D_416, C_417), C_418) | ~m1_subset_1(C_418, k1_zfmisc_1(u1_struct_0(A_415))) | ~m1_subset_1(k3_orders_2(A_415, D_416, C_417), k1_zfmisc_1(u1_struct_0(A_415))))), inference(resolution, [status(thm)], [c_8, c_909])).
% 16.05/9.07  tff(c_4, plain, (![A_5, B_6, C_10]: (~r2_hidden('#skF_1'(A_5, B_6, C_10), C_10) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.05/9.07  tff(c_1783, plain, (![C_489, A_490, D_491]: (~m1_subset_1(C_489, u1_struct_0(A_490)) | ~l1_orders_2(A_490) | ~v5_orders_2(A_490) | ~v4_orders_2(A_490) | ~v3_orders_2(A_490) | v2_struct_0(A_490) | r1_tarski(k3_orders_2(A_490, D_491, C_489), D_491) | ~m1_subset_1(D_491, k1_zfmisc_1(u1_struct_0(A_490))) | ~m1_subset_1(k3_orders_2(A_490, D_491, C_489), k1_zfmisc_1(u1_struct_0(A_490))))), inference(resolution, [status(thm)], [c_1532, c_4])).
% 16.05/9.07  tff(c_1791, plain, (![A_492, B_493, C_494]: (r1_tarski(k3_orders_2(A_492, B_493, C_494), B_493) | ~m1_subset_1(C_494, u1_struct_0(A_492)) | ~m1_subset_1(B_493, k1_zfmisc_1(u1_struct_0(A_492))) | ~l1_orders_2(A_492) | ~v5_orders_2(A_492) | ~v4_orders_2(A_492) | ~v3_orders_2(A_492) | v2_struct_0(A_492))), inference(resolution, [status(thm)], [c_14, c_1783])).
% 16.05/9.07  tff(c_1806, plain, (![A_492, A_12, C_494]: (r1_tarski(k3_orders_2(A_492, A_12, C_494), A_12) | ~m1_subset_1(C_494, u1_struct_0(A_492)) | ~l1_orders_2(A_492) | ~v5_orders_2(A_492) | ~v4_orders_2(A_492) | ~v3_orders_2(A_492) | v2_struct_0(A_492) | ~r1_tarski(A_12, u1_struct_0(A_492)))), inference(resolution, [status(thm)], [c_12, c_1791])).
% 16.05/9.07  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.05/9.07  tff(c_57, plain, (![A_53, B_54, C_55]: (r2_hidden('#skF_1'(A_53, B_54, C_55), B_54) | r1_tarski(B_54, C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.05/9.07  tff(c_66, plain, (![B_56, A_57]: (r1_tarski(B_56, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_57, c_4])).
% 16.05/9.07  tff(c_74, plain, (r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_26, c_66])).
% 16.05/9.07  tff(c_41, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | ~m1_subset_1(A_43, k1_zfmisc_1(B_44)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.05/9.07  tff(c_48, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_41])).
% 16.05/9.07  tff(c_1803, plain, (![C_494]: (r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_494), '#skF_4') | ~m1_subset_1(C_494, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_1791])).
% 16.05/9.07  tff(c_1813, plain, (![C_494]: (r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_494), '#skF_4') | ~m1_subset_1(C_494, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_1803])).
% 16.05/9.07  tff(c_1837, plain, (![C_496]: (r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_496), '#skF_4') | ~m1_subset_1(C_496, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_1813])).
% 16.05/9.07  tff(c_24, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 16.05/9.07  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.05/9.07  tff(c_111, plain, (![A_66, B_67, C_68, A_69]: (r2_hidden('#skF_1'(A_66, B_67, C_68), A_69) | ~m1_subset_1(B_67, k1_zfmisc_1(A_69)) | r1_tarski(B_67, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(A_66)) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(resolution, [status(thm)], [c_57, c_2])).
% 16.05/9.07  tff(c_132, plain, (![A_76, A_77, C_80, B_79, A_78]: (r2_hidden('#skF_1'(A_77, B_79, C_80), A_78) | ~m1_subset_1(A_76, k1_zfmisc_1(A_78)) | ~m1_subset_1(B_79, k1_zfmisc_1(A_76)) | r1_tarski(B_79, C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(A_77)) | ~m1_subset_1(B_79, k1_zfmisc_1(A_77)))), inference(resolution, [status(thm)], [c_111, c_2])).
% 16.05/9.07  tff(c_226, plain, (![B_107, B_103, A_105, A_104, C_106]: (r2_hidden('#skF_1'(A_104, B_107, C_106), B_103) | ~m1_subset_1(B_107, k1_zfmisc_1(A_105)) | r1_tarski(B_107, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(A_104)) | ~m1_subset_1(B_107, k1_zfmisc_1(A_104)) | ~r1_tarski(A_105, B_103))), inference(resolution, [status(thm)], [c_12, c_132])).
% 16.05/9.07  tff(c_349, plain, (![A_134, C_136, A_133, B_132, B_135]: (r2_hidden('#skF_1'(A_134, A_133, C_136), B_135) | r1_tarski(A_133, C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(A_134)) | ~m1_subset_1(A_133, k1_zfmisc_1(A_134)) | ~r1_tarski(B_132, B_135) | ~r1_tarski(A_133, B_132))), inference(resolution, [status(thm)], [c_12, c_226])).
% 16.05/9.07  tff(c_380, plain, (![A_140, A_141, C_142]: (r2_hidden('#skF_1'(A_140, A_141, C_142), '#skF_5') | r1_tarski(A_141, C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(A_140)) | ~m1_subset_1(A_141, k1_zfmisc_1(A_140)) | ~r1_tarski(A_141, '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_349])).
% 16.05/9.07  tff(c_792, plain, (![A_217, A_218, C_219, A_220]: (r2_hidden('#skF_1'(A_217, A_218, C_219), A_220) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_220)) | r1_tarski(A_218, C_219) | ~m1_subset_1(C_219, k1_zfmisc_1(A_217)) | ~m1_subset_1(A_218, k1_zfmisc_1(A_217)) | ~r1_tarski(A_218, '#skF_4'))), inference(resolution, [status(thm)], [c_380, c_2])).
% 16.05/9.07  tff(c_809, plain, (![A_221, A_222, A_223]: (~m1_subset_1('#skF_5', k1_zfmisc_1(A_221)) | r1_tarski(A_222, A_221) | ~m1_subset_1(A_221, k1_zfmisc_1(A_223)) | ~m1_subset_1(A_222, k1_zfmisc_1(A_223)) | ~r1_tarski(A_222, '#skF_4'))), inference(resolution, [status(thm)], [c_792, c_4])).
% 16.05/9.07  tff(c_829, plain, (![A_227, B_228, A_229]: (r1_tarski(A_227, B_228) | ~m1_subset_1(B_228, k1_zfmisc_1(A_229)) | ~m1_subset_1(A_227, k1_zfmisc_1(A_229)) | ~r1_tarski(A_227, '#skF_4') | ~r1_tarski('#skF_5', B_228))), inference(resolution, [status(thm)], [c_12, c_809])).
% 16.05/9.07  tff(c_848, plain, (![A_230, A_231, B_232]: (r1_tarski(A_230, A_231) | ~m1_subset_1(A_230, k1_zfmisc_1(B_232)) | ~r1_tarski(A_230, '#skF_4') | ~r1_tarski('#skF_5', A_231) | ~r1_tarski(A_231, B_232))), inference(resolution, [status(thm)], [c_12, c_829])).
% 16.05/9.07  tff(c_862, plain, (![A_12, A_231, B_13]: (r1_tarski(A_12, A_231) | ~r1_tarski(A_12, '#skF_4') | ~r1_tarski('#skF_5', A_231) | ~r1_tarski(A_231, B_13) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_12, c_848])).
% 16.05/9.07  tff(c_1962, plain, (![C_502, A_503, B_504]: (r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_502), A_503) | ~r1_tarski('#skF_5', A_503) | ~r1_tarski(A_503, B_504) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_502), B_504) | ~m1_subset_1(C_502, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1837, c_862])).
% 16.05/9.07  tff(c_2002, plain, (![C_502]: (r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_502), '#skF_5') | ~r1_tarski('#skF_5', '#skF_5') | ~r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_502), u1_struct_0('#skF_2')) | ~m1_subset_1(C_502, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_1962])).
% 16.05/9.07  tff(c_2030, plain, (![C_505]: (r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_505), '#skF_5') | ~r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_505), u1_struct_0('#skF_2')) | ~m1_subset_1(C_505, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2002])).
% 16.05/9.07  tff(c_2034, plain, (![C_75]: (r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_75), '#skF_5') | ~m1_subset_1(C_75, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_131, c_2030])).
% 16.05/9.07  tff(c_2037, plain, (![C_75]: (r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_75), '#skF_5') | ~m1_subset_1(C_75, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_2034])).
% 16.05/9.07  tff(c_2038, plain, (![C_75]: (r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_75), '#skF_5') | ~m1_subset_1(C_75, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_2037])).
% 16.05/9.07  tff(c_1801, plain, (![C_494]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_494), '#skF_5') | ~m1_subset_1(C_494, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_1791])).
% 16.05/9.07  tff(c_1809, plain, (![C_494]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_494), '#skF_5') | ~m1_subset_1(C_494, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_1801])).
% 16.05/9.07  tff(c_1810, plain, (![C_494]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_494), '#skF_5') | ~m1_subset_1(C_494, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_1809])).
% 16.05/9.07  tff(c_75, plain, (r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_66])).
% 16.05/9.07  tff(c_371, plain, (![A_137, A_138, C_139]: (r2_hidden('#skF_1'(A_137, A_138, C_139), '#skF_4') | r1_tarski(A_138, C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(A_137)) | ~m1_subset_1(A_138, k1_zfmisc_1(A_137)) | ~r1_tarski(A_138, '#skF_4'))), inference(resolution, [status(thm)], [c_75, c_349])).
% 16.05/9.07  tff(c_696, plain, (![A_193, A_194, C_195, A_196]: (r2_hidden('#skF_1'(A_193, A_194, C_195), A_196) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_196)) | r1_tarski(A_194, C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(A_193)) | ~m1_subset_1(A_194, k1_zfmisc_1(A_193)) | ~r1_tarski(A_194, '#skF_4'))), inference(resolution, [status(thm)], [c_371, c_2])).
% 16.05/9.07  tff(c_720, plain, (![A_200, A_201, A_202]: (~m1_subset_1('#skF_4', k1_zfmisc_1(A_200)) | r1_tarski(A_201, A_200) | ~m1_subset_1(A_200, k1_zfmisc_1(A_202)) | ~m1_subset_1(A_201, k1_zfmisc_1(A_202)) | ~r1_tarski(A_201, '#skF_4'))), inference(resolution, [status(thm)], [c_696, c_4])).
% 16.05/9.07  tff(c_728, plain, (![A_203, B_204, A_205]: (r1_tarski(A_203, B_204) | ~m1_subset_1(B_204, k1_zfmisc_1(A_205)) | ~m1_subset_1(A_203, k1_zfmisc_1(A_205)) | ~r1_tarski(A_203, '#skF_4') | ~r1_tarski('#skF_4', B_204))), inference(resolution, [status(thm)], [c_12, c_720])).
% 16.05/9.07  tff(c_749, plain, (![A_206, A_207, B_208]: (r1_tarski(A_206, A_207) | ~m1_subset_1(A_206, k1_zfmisc_1(B_208)) | ~r1_tarski(A_206, '#skF_4') | ~r1_tarski('#skF_4', A_207) | ~r1_tarski(A_207, B_208))), inference(resolution, [status(thm)], [c_12, c_728])).
% 16.05/9.07  tff(c_763, plain, (![A_12, A_207, B_13]: (r1_tarski(A_12, A_207) | ~r1_tarski(A_12, '#skF_4') | ~r1_tarski('#skF_4', A_207) | ~r1_tarski(A_207, B_13) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_12, c_749])).
% 16.05/9.07  tff(c_2075, plain, (![C_510, A_511, B_512]: (r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_510), A_511) | ~r1_tarski('#skF_4', A_511) | ~r1_tarski(A_511, B_512) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_510), B_512) | ~m1_subset_1(C_510, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1837, c_763])).
% 16.05/9.07  tff(c_2460, plain, (![C_544, C_545]: (r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_544), k3_orders_2('#skF_2', '#skF_5', C_545)) | ~r1_tarski('#skF_4', k3_orders_2('#skF_2', '#skF_5', C_545)) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_544), '#skF_5') | ~m1_subset_1(C_544, u1_struct_0('#skF_2')) | ~m1_subset_1(C_545, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1810, c_2075])).
% 16.05/9.07  tff(c_2485, plain, (~r1_tarski('#skF_4', k3_orders_2('#skF_2', '#skF_5', '#skF_3')) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2460, c_22])).
% 16.05/9.07  tff(c_2499, plain, (~r1_tarski('#skF_4', k3_orders_2('#skF_2', '#skF_5', '#skF_3')) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2485])).
% 16.05/9.07  tff(c_2509, plain, (~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_2499])).
% 16.05/9.07  tff(c_2512, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2038, c_2509])).
% 16.05/9.07  tff(c_2519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2512])).
% 16.05/9.07  tff(c_2521, plain, (r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_2499])).
% 16.05/9.07  tff(c_240, plain, (![B_103, A_104, C_106, A_12, B_13]: (r2_hidden('#skF_1'(A_104, A_12, C_106), B_103) | r1_tarski(A_12, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(A_104)) | ~m1_subset_1(A_12, k1_zfmisc_1(A_104)) | ~r1_tarski(B_13, B_103) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_12, c_226])).
% 16.05/9.07  tff(c_3036, plain, (![A_572, A_573, C_574]: (r2_hidden('#skF_1'(A_572, A_573, C_574), '#skF_5') | r1_tarski(A_573, C_574) | ~m1_subset_1(C_574, k1_zfmisc_1(A_572)) | ~m1_subset_1(A_573, k1_zfmisc_1(A_572)) | ~r1_tarski(A_573, k3_orders_2('#skF_2', '#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_2521, c_240])).
% 16.05/9.07  tff(c_3045, plain, (![A_575, A_576]: (r1_tarski(A_575, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_576)) | ~m1_subset_1(A_575, k1_zfmisc_1(A_576)) | ~r1_tarski(A_575, k3_orders_2('#skF_2', '#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_3036, c_4])).
% 16.05/9.07  tff(c_3053, plain, (![A_577]: (r1_tarski(A_577, '#skF_5') | ~m1_subset_1(A_577, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_577, k3_orders_2('#skF_2', '#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_26, c_3045])).
% 16.05/9.07  tff(c_3057, plain, (![B_15, C_16]: (r1_tarski(k3_orders_2('#skF_2', B_15, C_16), '#skF_5') | ~r1_tarski(k3_orders_2('#skF_2', B_15, C_16), k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | ~m1_subset_1(C_16, u1_struct_0('#skF_2')) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_3053])).
% 16.05/9.07  tff(c_3074, plain, (![B_15, C_16]: (r1_tarski(k3_orders_2('#skF_2', B_15, C_16), '#skF_5') | ~r1_tarski(k3_orders_2('#skF_2', B_15, C_16), k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | ~m1_subset_1(C_16, u1_struct_0('#skF_2')) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_3057])).
% 16.05/9.07  tff(c_3082, plain, (![B_578, C_579]: (r1_tarski(k3_orders_2('#skF_2', B_578, C_579), '#skF_5') | ~r1_tarski(k3_orders_2('#skF_2', B_578, C_579), k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | ~m1_subset_1(C_579, u1_struct_0('#skF_2')) | ~m1_subset_1(B_578, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_3074])).
% 16.05/9.07  tff(c_3101, plain, (![C_494]: (r1_tarski(k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_494), '#skF_5') | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_494, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1806, c_3082])).
% 16.05/9.07  tff(c_3125, plain, (![C_494]: (r1_tarski(k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_494), '#skF_5') | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_494, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_3101])).
% 16.05/9.07  tff(c_3126, plain, (![C_494]: (r1_tarski(k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_494), '#skF_5') | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_494, u1_struct_0('#skF_2')) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_3125])).
% 16.05/9.07  tff(c_3264, plain, (~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_3126])).
% 16.05/9.07  tff(c_3267, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_131, c_3264])).
% 16.05/9.07  tff(c_3270, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_30, c_3267])).
% 16.05/9.07  tff(c_3272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_3270])).
% 16.05/9.07  tff(c_3273, plain, (![C_494]: (~m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski(k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_494), '#skF_5') | ~m1_subset_1(C_494, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_3126])).
% 16.05/9.07  tff(c_3326, plain, (~m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_3273])).
% 16.05/9.07  tff(c_3329, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_3326])).
% 16.05/9.07  tff(c_3335, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_30, c_3329])).
% 16.05/9.07  tff(c_3337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_3335])).
% 16.05/9.07  tff(c_3339, plain, (m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_3273])).
% 16.05/9.07  tff(c_73, plain, (![A_12, B_13]: (r1_tarski(A_12, A_12) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_12, c_66])).
% 16.05/9.07  tff(c_2557, plain, (r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_2521, c_73])).
% 16.05/9.07  tff(c_1789, plain, (![A_14, B_15, C_16]: (r1_tarski(k3_orders_2(A_14, B_15, C_16), B_15) | ~m1_subset_1(C_16, u1_struct_0(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_orders_2(A_14) | ~v5_orders_2(A_14) | ~v4_orders_2(A_14) | ~v3_orders_2(A_14) | v2_struct_0(A_14))), inference(resolution, [status(thm)], [c_14, c_1783])).
% 16.05/9.07  tff(c_3348, plain, (![C_16]: (r1_tarski(k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_16), k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | ~m1_subset_1(C_16, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_3339, c_1789])).
% 16.05/9.07  tff(c_3436, plain, (![C_16]: (r1_tarski(k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_16), k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | ~m1_subset_1(C_16, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_3348])).
% 16.05/9.07  tff(c_3437, plain, (![C_16]: (r1_tarski(k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_16), k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | ~m1_subset_1(C_16, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_3436])).
% 16.05/9.07  tff(c_3274, plain, (r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_3126])).
% 16.05/9.07  tff(c_5391, plain, (![A_679, A_680, C_681]: (r2_hidden('#skF_1'(A_679, A_680, C_681), k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | r1_tarski(A_680, C_681) | ~m1_subset_1(C_681, k1_zfmisc_1(A_679)) | ~m1_subset_1(A_680, k1_zfmisc_1(A_679)) | ~r1_tarski(A_680, k3_orders_2('#skF_2', '#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_2557, c_240])).
% 16.05/9.07  tff(c_20, plain, (![A_17, B_25, C_29, D_31]: (r2_orders_2(A_17, B_25, C_29) | ~r2_hidden(B_25, k3_orders_2(A_17, D_31, C_29)) | ~m1_subset_1(D_31, k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(C_29, u1_struct_0(A_17)) | ~m1_subset_1(B_25, u1_struct_0(A_17)) | ~l1_orders_2(A_17) | ~v5_orders_2(A_17) | ~v4_orders_2(A_17) | ~v3_orders_2(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.05/9.07  tff(c_5401, plain, (![A_679, A_680, C_681]: (r2_orders_2('#skF_2', '#skF_1'(A_679, A_680, C_681), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_679, A_680, C_681), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(A_680, C_681) | ~m1_subset_1(C_681, k1_zfmisc_1(A_679)) | ~m1_subset_1(A_680, k1_zfmisc_1(A_679)) | ~r1_tarski(A_680, k3_orders_2('#skF_2', '#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_5391, c_20])).
% 16.05/9.07  tff(c_5418, plain, (![A_679, A_680, C_681]: (r2_orders_2('#skF_2', '#skF_1'(A_679, A_680, C_681), '#skF_3') | ~m1_subset_1('#skF_1'(A_679, A_680, C_681), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_tarski(A_680, C_681) | ~m1_subset_1(C_681, k1_zfmisc_1(A_679)) | ~m1_subset_1(A_680, k1_zfmisc_1(A_679)) | ~r1_tarski(A_680, k3_orders_2('#skF_2', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_28, c_5401])).
% 16.05/9.07  tff(c_6962, plain, (![A_788, A_789, C_790]: (r2_orders_2('#skF_2', '#skF_1'(A_788, A_789, C_790), '#skF_3') | ~m1_subset_1('#skF_1'(A_788, A_789, C_790), u1_struct_0('#skF_2')) | r1_tarski(A_789, C_790) | ~m1_subset_1(C_790, k1_zfmisc_1(A_788)) | ~m1_subset_1(A_789, k1_zfmisc_1(A_788)) | ~r1_tarski(A_789, k3_orders_2('#skF_2', '#skF_4', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_5418])).
% 16.05/9.07  tff(c_6967, plain, (![B_6, C_10]: (r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_6, C_10), '#skF_3') | ~r1_tarski(B_6, k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_6962])).
% 16.05/9.07  tff(c_397, plain, (![B_145, A_146, D_147, C_148]: (r2_hidden(B_145, k3_orders_2(A_146, D_147, C_148)) | ~r2_hidden(B_145, D_147) | ~r2_orders_2(A_146, B_145, C_148) | ~m1_subset_1(D_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~m1_subset_1(C_148, u1_struct_0(A_146)) | ~m1_subset_1(B_145, u1_struct_0(A_146)) | ~l1_orders_2(A_146) | ~v5_orders_2(A_146) | ~v4_orders_2(A_146) | ~v3_orders_2(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.05/9.07  tff(c_674, plain, (![B_187, A_188, A_189, C_190]: (r2_hidden(B_187, k3_orders_2(A_188, A_189, C_190)) | ~r2_hidden(B_187, A_189) | ~r2_orders_2(A_188, B_187, C_190) | ~m1_subset_1(C_190, u1_struct_0(A_188)) | ~m1_subset_1(B_187, u1_struct_0(A_188)) | ~l1_orders_2(A_188) | ~v5_orders_2(A_188) | ~v4_orders_2(A_188) | ~v3_orders_2(A_188) | v2_struct_0(A_188) | ~r1_tarski(A_189, u1_struct_0(A_188)))), inference(resolution, [status(thm)], [c_12, c_397])).
% 16.05/9.07  tff(c_3505, plain, (![A_592, C_595, A_594, B_591, A_593]: (r1_tarski(B_591, k3_orders_2(A_593, A_594, C_595)) | ~m1_subset_1(k3_orders_2(A_593, A_594, C_595), k1_zfmisc_1(A_592)) | ~m1_subset_1(B_591, k1_zfmisc_1(A_592)) | ~r2_hidden('#skF_1'(A_592, B_591, k3_orders_2(A_593, A_594, C_595)), A_594) | ~r2_orders_2(A_593, '#skF_1'(A_592, B_591, k3_orders_2(A_593, A_594, C_595)), C_595) | ~m1_subset_1(C_595, u1_struct_0(A_593)) | ~m1_subset_1('#skF_1'(A_592, B_591, k3_orders_2(A_593, A_594, C_595)), u1_struct_0(A_593)) | ~l1_orders_2(A_593) | ~v5_orders_2(A_593) | ~v4_orders_2(A_593) | ~v3_orders_2(A_593) | v2_struct_0(A_593) | ~r1_tarski(A_594, u1_struct_0(A_593)))), inference(resolution, [status(thm)], [c_674, c_4])).
% 16.05/9.07  tff(c_7854, plain, (![A_823, A_824, B_825, C_826]: (~r2_orders_2(A_823, '#skF_1'(A_824, B_825, k3_orders_2(A_823, B_825, C_826)), C_826) | ~m1_subset_1(C_826, u1_struct_0(A_823)) | ~m1_subset_1('#skF_1'(A_824, B_825, k3_orders_2(A_823, B_825, C_826)), u1_struct_0(A_823)) | ~l1_orders_2(A_823) | ~v5_orders_2(A_823) | ~v4_orders_2(A_823) | ~v3_orders_2(A_823) | v2_struct_0(A_823) | ~r1_tarski(B_825, u1_struct_0(A_823)) | r1_tarski(B_825, k3_orders_2(A_823, B_825, C_826)) | ~m1_subset_1(k3_orders_2(A_823, B_825, C_826), k1_zfmisc_1(A_824)) | ~m1_subset_1(B_825, k1_zfmisc_1(A_824)))), inference(resolution, [status(thm)], [c_6, c_3505])).
% 16.05/9.07  tff(c_7857, plain, (![B_6]: (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_6, k3_orders_2('#skF_2', B_6, '#skF_3')), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(B_6, u1_struct_0('#skF_2')) | ~r1_tarski(B_6, k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | r1_tarski(B_6, k3_orders_2('#skF_2', B_6, '#skF_3')) | ~m1_subset_1(k3_orders_2('#skF_2', B_6, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_6967, c_7854])).
% 16.05/9.07  tff(c_7863, plain, (![B_6]: (~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_6, k3_orders_2('#skF_2', B_6, '#skF_3')), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(B_6, u1_struct_0('#skF_2')) | ~r1_tarski(B_6, k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | r1_tarski(B_6, k3_orders_2('#skF_2', B_6, '#skF_3')) | ~m1_subset_1(k3_orders_2('#skF_2', B_6, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_7857])).
% 16.05/9.07  tff(c_14353, plain, (![B_1158]: (~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_1158, k3_orders_2('#skF_2', B_1158, '#skF_3')), u1_struct_0('#skF_2')) | ~r1_tarski(B_1158, u1_struct_0('#skF_2')) | ~r1_tarski(B_1158, k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | r1_tarski(B_1158, k3_orders_2('#skF_2', B_1158, '#skF_3')) | ~m1_subset_1(k3_orders_2('#skF_2', B_1158, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1158, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_7863])).
% 16.05/9.07  tff(c_14851, plain, (![B_1183]: (~r1_tarski(B_1183, u1_struct_0('#skF_2')) | ~r1_tarski(B_1183, k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | r1_tarski(B_1183, k3_orders_2('#skF_2', B_1183, '#skF_3')) | ~m1_subset_1(k3_orders_2('#skF_2', B_1183, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1183, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_14353])).
% 16.05/9.07  tff(c_14856, plain, (![B_15]: (~r1_tarski(B_15, u1_struct_0('#skF_2')) | ~r1_tarski(B_15, k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | r1_tarski(B_15, k3_orders_2('#skF_2', B_15, '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_14851])).
% 16.05/9.07  tff(c_14866, plain, (![B_15]: (~r1_tarski(B_15, u1_struct_0('#skF_2')) | ~r1_tarski(B_15, k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | r1_tarski(B_15, k3_orders_2('#skF_2', B_15, '#skF_3')) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_14856])).
% 16.05/9.07  tff(c_14869, plain, (![B_1184]: (~r1_tarski(B_1184, u1_struct_0('#skF_2')) | ~r1_tarski(B_1184, k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | r1_tarski(B_1184, k3_orders_2('#skF_2', B_1184, '#skF_3')) | ~m1_subset_1(B_1184, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_14866])).
% 16.05/9.07  tff(c_14871, plain, (~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_3'))), inference(resolution, [status(thm)], [c_3339, c_14869])).
% 16.05/9.07  tff(c_14887, plain, (r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_3274, c_14871])).
% 16.05/9.07  tff(c_15191, plain, (![A_1192, A_1193, C_1194]: (r2_hidden('#skF_1'(A_1192, A_1193, C_1194), k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_3')) | r1_tarski(A_1193, C_1194) | ~m1_subset_1(C_1194, k1_zfmisc_1(A_1192)) | ~m1_subset_1(A_1193, k1_zfmisc_1(A_1192)) | ~r1_tarski(A_1193, k3_orders_2('#skF_2', '#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_14887, c_240])).
% 16.05/9.07  tff(c_15232, plain, (![A_1195, A_1196]: (r1_tarski(A_1195, k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_3')) | ~m1_subset_1(k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_3'), k1_zfmisc_1(A_1196)) | ~m1_subset_1(A_1195, k1_zfmisc_1(A_1196)) | ~r1_tarski(A_1195, k3_orders_2('#skF_2', '#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_15191, c_4])).
% 16.05/9.07  tff(c_15653, plain, (![A_1209, B_1210]: (r1_tarski(A_1209, k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_3')) | ~m1_subset_1(A_1209, k1_zfmisc_1(B_1210)) | ~r1_tarski(A_1209, k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | ~r1_tarski(k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_3'), B_1210))), inference(resolution, [status(thm)], [c_12, c_15232])).
% 16.05/9.07  tff(c_15675, plain, (![A_1211, B_1212]: (r1_tarski(A_1211, k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_3')) | ~r1_tarski(A_1211, k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | ~r1_tarski(k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_3'), B_1212) | ~r1_tarski(A_1211, B_1212))), inference(resolution, [status(thm)], [c_12, c_15653])).
% 16.05/9.07  tff(c_15690, plain, (![A_1211]: (r1_tarski(A_1211, k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_3')) | ~r1_tarski(A_1211, k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_3437, c_15675])).
% 16.05/9.07  tff(c_15750, plain, (![A_1213]: (r1_tarski(A_1213, k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_3')) | ~r1_tarski(A_1213, k3_orders_2('#skF_2', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_15690])).
% 16.05/9.07  tff(c_17718, plain, (![A_1258, A_1259, C_1260, A_1261]: (r2_hidden('#skF_1'(A_1258, A_1259, C_1260), k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_3')) | r1_tarski(A_1259, C_1260) | ~m1_subset_1(C_1260, k1_zfmisc_1(A_1258)) | ~m1_subset_1(A_1259, k1_zfmisc_1(A_1258)) | ~r1_tarski(A_1259, A_1261) | ~r1_tarski(A_1261, k3_orders_2('#skF_2', '#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_15750, c_240])).
% 16.05/9.07  tff(c_17810, plain, (![A_1258, C_1260]: (r2_hidden('#skF_1'(A_1258, k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_1260), k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_3')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_1260) | ~m1_subset_1(C_1260, k1_zfmisc_1(A_1258)) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(A_1258)) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_2557, c_17718])).
% 16.05/9.07  tff(c_18036, plain, (![A_1264, C_1265]: (r2_hidden('#skF_1'(A_1264, k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_1265), k3_orders_2('#skF_2', k3_orders_2('#skF_2', '#skF_4', '#skF_3'), '#skF_3')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_1265) | ~m1_subset_1(C_1265, k1_zfmisc_1(A_1264)) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(A_1264)))), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_17810])).
% 16.05/9.07  tff(c_18048, plain, (![A_1264, C_1265]: (r2_orders_2('#skF_2', '#skF_1'(A_1264, k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_1265), '#skF_3') | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_1264, k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_1265), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_1265) | ~m1_subset_1(C_1265, k1_zfmisc_1(A_1264)) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(A_1264)))), inference(resolution, [status(thm)], [c_18036, c_20])).
% 16.05/9.07  tff(c_18069, plain, (![A_1264, C_1265]: (r2_orders_2('#skF_2', '#skF_1'(A_1264, k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_1265), '#skF_3') | ~m1_subset_1('#skF_1'(A_1264, k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_1265), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_1265) | ~m1_subset_1(C_1265, k1_zfmisc_1(A_1264)) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(A_1264)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_3339, c_18048])).
% 16.05/9.07  tff(c_18849, plain, (![A_1305, C_1306]: (r2_orders_2('#skF_2', '#skF_1'(A_1305, k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_1306), '#skF_3') | ~m1_subset_1('#skF_1'(A_1305, k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_1306), u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_1306) | ~m1_subset_1(C_1306, k1_zfmisc_1(A_1305)) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(A_1305)))), inference(negUnitSimplification, [status(thm)], [c_40, c_18069])).
% 16.05/9.07  tff(c_18853, plain, (![C_10]: (r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_10), '#skF_3') | r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_18849])).
% 16.05/9.07  tff(c_18857, plain, (![C_1307]: (r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_1307), '#skF_3') | r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), C_1307) | ~m1_subset_1(C_1307, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_3339, c_18853])).
% 16.05/9.07  tff(c_407, plain, (![B_145, C_148]: (r2_hidden(B_145, k3_orders_2('#skF_2', '#skF_5', C_148)) | ~r2_hidden(B_145, '#skF_5') | ~r2_orders_2('#skF_2', B_145, C_148) | ~m1_subset_1(C_148, u1_struct_0('#skF_2')) | ~m1_subset_1(B_145, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_397])).
% 16.05/9.07  tff(c_415, plain, (![B_145, C_148]: (r2_hidden(B_145, k3_orders_2('#skF_2', '#skF_5', C_148)) | ~r2_hidden(B_145, '#skF_5') | ~r2_orders_2('#skF_2', B_145, C_148) | ~m1_subset_1(C_148, u1_struct_0('#skF_2')) | ~m1_subset_1(B_145, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_407])).
% 16.05/9.07  tff(c_494, plain, (![B_153, C_154]: (r2_hidden(B_153, k3_orders_2('#skF_2', '#skF_5', C_154)) | ~r2_hidden(B_153, '#skF_5') | ~r2_orders_2('#skF_2', B_153, C_154) | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_153, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_415])).
% 16.05/9.07  tff(c_513, plain, (![B_6, C_154, A_5]: (r1_tarski(B_6, k3_orders_2('#skF_2', '#skF_5', C_154)) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_154), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)) | ~r2_hidden('#skF_1'(A_5, B_6, k3_orders_2('#skF_2', '#skF_5', C_154)), '#skF_5') | ~r2_orders_2('#skF_2', '#skF_1'(A_5, B_6, k3_orders_2('#skF_2', '#skF_5', C_154)), C_154) | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_5, B_6, k3_orders_2('#skF_2', '#skF_5', C_154)), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_494, c_4])).
% 16.05/9.07  tff(c_18907, plain, (~m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_18857, c_513])).
% 16.05/9.07  tff(c_18979, plain, (~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3339, c_18907])).
% 16.05/9.07  tff(c_18980, plain, (~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_22, c_18979])).
% 16.05/9.07  tff(c_19513, plain, (~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_18980])).
% 16.05/9.07  tff(c_19516, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_19513])).
% 16.05/9.07  tff(c_19522, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_26, c_30, c_19516])).
% 16.05/9.07  tff(c_19524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_19522])).
% 16.05/9.07  tff(c_19526, plain, (m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_18980])).
% 16.05/9.07  tff(c_64, plain, (![B_54, A_53]: (r1_tarski(B_54, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(resolution, [status(thm)], [c_57, c_4])).
% 16.05/9.07  tff(c_130, plain, (![A_73, B_74, C_75]: (r1_tarski(k3_orders_2(A_73, B_74, C_75), k3_orders_2(A_73, B_74, C_75)) | ~m1_subset_1(C_75, u1_struct_0(A_73)) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(resolution, [status(thm)], [c_124, c_64])).
% 16.05/9.07  tff(c_1815, plain, (![C_495]: (r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_495), '#skF_5') | ~m1_subset_1(C_495, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_1809])).
% 16.05/9.07  tff(c_2343, plain, (![A_526, A_527, C_528, C_529]: (r2_hidden('#skF_1'(A_526, A_527, C_528), '#skF_5') | r1_tarski(A_527, C_528) | ~m1_subset_1(C_528, k1_zfmisc_1(A_526)) | ~m1_subset_1(A_527, k1_zfmisc_1(A_526)) | ~r1_tarski(A_527, k3_orders_2('#skF_2', '#skF_5', C_529)) | ~m1_subset_1(C_529, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1815, c_240])).
% 16.05/9.07  tff(c_2351, plain, (![A_526, C_75, C_528]: (r2_hidden('#skF_1'(A_526, k3_orders_2('#skF_2', '#skF_5', C_75), C_528), '#skF_5') | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_75), C_528) | ~m1_subset_1(C_528, k1_zfmisc_1(A_526)) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_75), k1_zfmisc_1(A_526)) | ~m1_subset_1(C_75, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_130, c_2343])).
% 16.05/9.07  tff(c_2359, plain, (![A_526, C_75, C_528]: (r2_hidden('#skF_1'(A_526, k3_orders_2('#skF_2', '#skF_5', C_75), C_528), '#skF_5') | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_75), C_528) | ~m1_subset_1(C_528, k1_zfmisc_1(A_526)) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_75), k1_zfmisc_1(A_526)) | ~m1_subset_1(C_75, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_26, c_2351])).
% 16.05/9.07  tff(c_2500, plain, (![A_546, C_547, C_548]: (r2_hidden('#skF_1'(A_546, k3_orders_2('#skF_2', '#skF_5', C_547), C_548), '#skF_5') | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_547), C_548) | ~m1_subset_1(C_548, k1_zfmisc_1(A_546)) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_547), k1_zfmisc_1(A_546)) | ~m1_subset_1(C_547, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_2359])).
% 16.05/9.07  tff(c_18211, plain, (![A_1280, C_1281, C_1282, A_1283]: (r2_hidden('#skF_1'(A_1280, k3_orders_2('#skF_2', '#skF_5', C_1281), C_1282), A_1283) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1283)) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_1281), C_1282) | ~m1_subset_1(C_1282, k1_zfmisc_1(A_1280)) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_1281), k1_zfmisc_1(A_1280)) | ~m1_subset_1(C_1281, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2500, c_2])).
% 16.05/9.07  tff(c_18259, plain, (![A_1284, C_1285, A_1286]: (~m1_subset_1('#skF_5', k1_zfmisc_1(A_1284)) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_1285), A_1284) | ~m1_subset_1(A_1284, k1_zfmisc_1(A_1286)) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_1285), k1_zfmisc_1(A_1286)) | ~m1_subset_1(C_1285, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_18211, c_4])).
% 16.05/9.07  tff(c_18276, plain, (![A_12, C_1285, B_13]: (~m1_subset_1('#skF_5', k1_zfmisc_1(A_12)) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_1285), A_12) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_1285), k1_zfmisc_1(B_13)) | ~m1_subset_1(C_1285, u1_struct_0('#skF_2')) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_12, c_18259])).
% 16.05/9.07  tff(c_19528, plain, (![A_12]: (~m1_subset_1('#skF_5', k1_zfmisc_1(A_12)) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), A_12) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~r1_tarski(A_12, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_19526, c_18276])).
% 16.05/9.07  tff(c_20046, plain, (![A_1328]: (~m1_subset_1('#skF_5', k1_zfmisc_1(A_1328)) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), A_1328) | ~r1_tarski(A_1328, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_19528])).
% 16.05/9.07  tff(c_20108, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_48, c_20046])).
% 16.05/9.07  tff(c_20109, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_20108])).
% 16.05/9.07  tff(c_20112, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_12, c_20109])).
% 16.05/9.07  tff(c_20116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_20112])).
% 16.05/9.07  tff(c_20118, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_20108])).
% 16.05/9.07  tff(c_5513, plain, (![A_693, A_694, C_695, A_696]: (r2_hidden('#skF_1'(A_693, A_694, C_695), A_696) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_696)) | r1_tarski(A_694, C_695) | ~m1_subset_1(C_695, k1_zfmisc_1(A_693)) | ~m1_subset_1(A_694, k1_zfmisc_1(A_693)) | ~r1_tarski(A_694, k3_orders_2('#skF_2', '#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_3036, c_2])).
% 16.05/9.07  tff(c_11048, plain, (![C_967, A_965, A_966, A_963, A_964]: (r2_hidden('#skF_1'(A_965, A_963, C_967), A_966) | ~m1_subset_1(A_964, k1_zfmisc_1(A_966)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_964)) | r1_tarski(A_963, C_967) | ~m1_subset_1(C_967, k1_zfmisc_1(A_965)) | ~m1_subset_1(A_963, k1_zfmisc_1(A_965)) | ~r1_tarski(A_963, k3_orders_2('#skF_2', '#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_5513, c_2])).
% 16.05/9.07  tff(c_11065, plain, (![C_967, A_965, A_12, B_13, A_963]: (r2_hidden('#skF_1'(A_965, A_963, C_967), B_13) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_12)) | r1_tarski(A_963, C_967) | ~m1_subset_1(C_967, k1_zfmisc_1(A_965)) | ~m1_subset_1(A_963, k1_zfmisc_1(A_965)) | ~r1_tarski(A_963, k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_12, c_11048])).
% 16.05/9.07  tff(c_20241, plain, (![A_965, A_963, C_967, B_13]: (r2_hidden('#skF_1'(A_965, A_963, C_967), B_13) | r1_tarski(A_963, C_967) | ~m1_subset_1(C_967, k1_zfmisc_1(A_965)) | ~m1_subset_1(A_963, k1_zfmisc_1(A_965)) | ~r1_tarski(A_963, k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | ~r1_tarski('#skF_5', B_13))), inference(resolution, [status(thm)], [c_20118, c_11065])).
% 16.05/9.07  tff(c_19525, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5')), inference(splitRight, [status(thm)], [c_18980])).
% 16.05/9.07  tff(c_27371, plain, (~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5')), inference(splitLeft, [status(thm)], [c_19525])).
% 16.05/9.07  tff(c_27490, plain, (r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_4', '#skF_3')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_20241, c_27371])).
% 16.05/9.07  tff(c_27562, plain, (r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2557, c_3339, c_19526, c_27490])).
% 16.05/9.07  tff(c_27564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_27562])).
% 16.05/9.07  tff(c_27565, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_19525])).
% 16.05/9.07  tff(c_27581, plain, (r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_27565])).
% 16.05/9.07  tff(c_27584, plain, (r1_tarski(k3_orders_2('#skF_2', '#skF_4', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3339, c_19526, c_27581])).
% 16.05/9.08  tff(c_27586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_27584])).
% 16.05/9.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.05/9.08  
% 16.05/9.08  Inference rules
% 16.05/9.08  ----------------------
% 16.05/9.08  #Ref     : 0
% 16.05/9.08  #Sup     : 6536
% 16.05/9.08  #Fact    : 0
% 16.05/9.08  #Define  : 0
% 16.05/9.08  #Split   : 27
% 16.05/9.08  #Chain   : 0
% 16.05/9.08  #Close   : 0
% 16.05/9.08  
% 16.05/9.08  Ordering : KBO
% 16.05/9.08  
% 16.05/9.08  Simplification rules
% 16.05/9.08  ----------------------
% 16.05/9.08  #Subsume      : 3558
% 16.05/9.08  #Demod        : 4910
% 16.05/9.08  #Tautology    : 571
% 16.05/9.08  #SimpNegUnit  : 494
% 16.05/9.08  #BackRed      : 0
% 16.05/9.08  
% 16.05/9.08  #Partial instantiations: 0
% 16.05/9.08  #Strategies tried      : 1
% 16.05/9.08  
% 16.05/9.08  Timing (in seconds)
% 16.05/9.08  ----------------------
% 16.05/9.08  Preprocessing        : 0.31
% 16.05/9.08  Parsing              : 0.17
% 16.05/9.08  CNF conversion       : 0.03
% 16.05/9.08  Main loop            : 7.97
% 16.05/9.08  Inferencing          : 1.21
% 16.05/9.08  Reduction            : 1.49
% 16.05/9.08  Demodulation         : 1.00
% 16.05/9.08  BG Simplification    : 0.08
% 16.05/9.08  Subsumption          : 4.88
% 16.05/9.08  Abstraction          : 0.17
% 16.05/9.08  MUC search           : 0.00
% 16.05/9.08  Cooper               : 0.00
% 16.05/9.08  Total                : 8.35
% 16.05/9.08  Index Insertion      : 0.00
% 16.05/9.08  Index Deletion       : 0.00
% 16.05/9.08  Index Matching       : 0.00
% 16.05/9.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
