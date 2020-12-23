%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:47 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 357 expanded)
%              Number of leaves         :   25 ( 152 expanded)
%              Depth                    :   18
%              Number of atoms          :  287 (2045 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   6 average)
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

tff(f_128,negated_conjecture,(
    ~ ! [A] :
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
                   => ( r2_orders_2(A,B,C)
                     => r1_tarski(k3_orders_2(A,D,B),k3_orders_2(A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_orders_2)).

tff(f_56,axiom,(
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

tff(f_39,axiom,(
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

tff(f_103,axiom,(
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

tff(f_77,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r2_orders_2(A,B,C)
                      & r2_orders_2(A,C,D) )
                   => r2_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_orders_2)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_32,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_30,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_28,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k3_orders_2(A_8,B_9,C_10),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(C_10,u1_struct_0(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ~ r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_6,plain,(
    ! [A_1,B_2,C_6] :
      ( m1_subset_1('#skF_1'(A_1,B_2,C_6),A_1)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_1,B_2,C_6] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_6),B_2)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( r2_orders_2(A_83,B_84,C_85)
      | ~ r2_hidden(B_84,k3_orders_2(A_83,D_86,C_85))
      | ~ m1_subset_1(D_86,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_subset_1(C_85,u1_struct_0(A_83))
      | ~ m1_subset_1(B_84,u1_struct_0(A_83))
      | ~ l1_orders_2(A_83)
      | ~ v5_orders_2(A_83)
      | ~ v4_orders_2(A_83)
      | ~ v3_orders_2(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_189,plain,(
    ! [A_134,A_133,C_130,D_132,C_131] :
      ( r2_orders_2(A_134,'#skF_1'(A_133,k3_orders_2(A_134,D_132,C_130),C_131),C_130)
      | ~ m1_subset_1(D_132,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_subset_1(C_130,u1_struct_0(A_134))
      | ~ m1_subset_1('#skF_1'(A_133,k3_orders_2(A_134,D_132,C_130),C_131),u1_struct_0(A_134))
      | ~ l1_orders_2(A_134)
      | ~ v5_orders_2(A_134)
      | ~ v4_orders_2(A_134)
      | ~ v3_orders_2(A_134)
      | v2_struct_0(A_134)
      | r1_tarski(k3_orders_2(A_134,D_132,C_130),C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(A_133))
      | ~ m1_subset_1(k3_orders_2(A_134,D_132,C_130),k1_zfmisc_1(A_133)) ) ),
    inference(resolution,[status(thm)],[c_4,c_87])).

tff(c_194,plain,(
    ! [A_135,D_136,C_137,C_138] :
      ( r2_orders_2(A_135,'#skF_1'(u1_struct_0(A_135),k3_orders_2(A_135,D_136,C_137),C_138),C_137)
      | ~ m1_subset_1(D_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_subset_1(C_137,u1_struct_0(A_135))
      | ~ l1_orders_2(A_135)
      | ~ v5_orders_2(A_135)
      | ~ v4_orders_2(A_135)
      | ~ v3_orders_2(A_135)
      | v2_struct_0(A_135)
      | r1_tarski(k3_orders_2(A_135,D_136,C_137),C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_subset_1(k3_orders_2(A_135,D_136,C_137),k1_zfmisc_1(u1_struct_0(A_135))) ) ),
    inference(resolution,[status(thm)],[c_6,c_189])).

tff(c_20,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_59,plain,(
    ! [A_72,B_73,D_74,C_75] :
      ( r2_orders_2(A_72,B_73,D_74)
      | ~ r2_orders_2(A_72,C_75,D_74)
      | ~ r2_orders_2(A_72,B_73,C_75)
      | ~ m1_subset_1(D_74,u1_struct_0(A_72))
      | ~ m1_subset_1(C_75,u1_struct_0(A_72))
      | ~ m1_subset_1(B_73,u1_struct_0(A_72))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_61,plain,(
    ! [B_73] :
      ( r2_orders_2('#skF_2',B_73,'#skF_4')
      | ~ r2_orders_2('#skF_2',B_73,'#skF_3')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_59])).

tff(c_65,plain,(
    ! [B_76] :
      ( r2_orders_2('#skF_2',B_76,'#skF_4')
      | ~ r2_orders_2('#skF_2',B_76,'#skF_3')
      | ~ m1_subset_1(B_76,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_61])).

tff(c_76,plain,(
    ! [B_2,C_6] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2,C_6),'#skF_4')
      | ~ r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2,C_6),'#skF_3')
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_201,plain,(
    ! [D_136,C_138] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_136,'#skF_3'),C_138),'#skF_4')
      | ~ m1_subset_1(D_136,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2',D_136,'#skF_3'),C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_136,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_194,c_76])).

tff(c_210,plain,(
    ! [D_136,C_138] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_136,'#skF_3'),C_138),'#skF_4')
      | ~ m1_subset_1(D_136,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2',D_136,'#skF_3'),C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_136,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_201])).

tff(c_213,plain,(
    ! [D_139,C_140] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_139,'#skF_3'),C_140),'#skF_4')
      | ~ m1_subset_1(D_139,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski(k3_orders_2('#skF_2',D_139,'#skF_3'),C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_139,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_210])).

tff(c_92,plain,(
    ! [B_87,A_88,D_89,C_90] :
      ( r2_hidden(B_87,k3_orders_2(A_88,D_89,C_90))
      | ~ r2_hidden(B_87,D_89)
      | ~ r2_orders_2(A_88,B_87,C_90)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(C_90,u1_struct_0(A_88))
      | ~ m1_subset_1(B_87,u1_struct_0(A_88))
      | ~ l1_orders_2(A_88)
      | ~ v5_orders_2(A_88)
      | ~ v4_orders_2(A_88)
      | ~ v3_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_99,plain,(
    ! [B_87,C_90] :
      ( r2_hidden(B_87,k3_orders_2('#skF_2','#skF_5',C_90))
      | ~ r2_hidden(B_87,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_87,C_90)
      | ~ m1_subset_1(C_90,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_92])).

tff(c_104,plain,(
    ! [B_87,C_90] :
      ( r2_hidden(B_87,k3_orders_2('#skF_2','#skF_5',C_90))
      | ~ r2_hidden(B_87,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_87,C_90)
      | ~ m1_subset_1(C_90,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_99])).

tff(c_106,plain,(
    ! [B_91,C_92] :
      ( r2_hidden(B_91,k3_orders_2('#skF_2','#skF_5',C_92))
      | ~ r2_hidden(B_91,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_91,C_92)
      | ~ m1_subset_1(C_92,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_91,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_104])).

tff(c_2,plain,(
    ! [A_1,B_2,C_6] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_6),C_6)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_123,plain,(
    ! [B_2,C_92,A_1] :
      ( r1_tarski(B_2,k3_orders_2('#skF_2','#skF_5',C_92))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_92),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1))
      | ~ r2_hidden('#skF_1'(A_1,B_2,k3_orders_2('#skF_2','#skF_5',C_92)),'#skF_5')
      | ~ r2_orders_2('#skF_2','#skF_1'(A_1,B_2,k3_orders_2('#skF_2','#skF_5',C_92)),C_92)
      | ~ m1_subset_1(C_92,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_1,B_2,k3_orders_2('#skF_2','#skF_5',C_92)),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_216,plain,(
    ! [D_139] :
      ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_139,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_139,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_139,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski(k3_orders_2('#skF_2',D_139,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_139,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_213,c_123])).

tff(c_221,plain,(
    ! [D_139] :
      ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_139,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_139,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_139,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski(k3_orders_2('#skF_2',D_139,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_139,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_216])).

tff(c_233,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_236,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_233])).

tff(c_239,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_22,c_24,c_236])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_239])).

tff(c_243,plain,(
    m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_82,plain,(
    ! [B_79,D_80,A_81,C_82] :
      ( r2_hidden(B_79,D_80)
      | ~ r2_hidden(B_79,k3_orders_2(A_81,D_80,C_82))
      | ~ m1_subset_1(D_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ m1_subset_1(C_82,u1_struct_0(A_81))
      | ~ m1_subset_1(B_79,u1_struct_0(A_81))
      | ~ l1_orders_2(A_81)
      | ~ v5_orders_2(A_81)
      | ~ v4_orders_2(A_81)
      | ~ v3_orders_2(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_137,plain,(
    ! [C_104,C_102,A_105,D_101,A_103] :
      ( r2_hidden('#skF_1'(A_105,k3_orders_2(A_103,D_101,C_102),C_104),D_101)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(C_102,u1_struct_0(A_103))
      | ~ m1_subset_1('#skF_1'(A_105,k3_orders_2(A_103,D_101,C_102),C_104),u1_struct_0(A_103))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103)
      | r1_tarski(k3_orders_2(A_103,D_101,C_102),C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(A_105))
      | ~ m1_subset_1(k3_orders_2(A_103,D_101,C_102),k1_zfmisc_1(A_105)) ) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_141,plain,(
    ! [A_103,D_101,C_102,C_6] :
      ( r2_hidden('#skF_1'(u1_struct_0(A_103),k3_orders_2(A_103,D_101,C_102),C_6),D_101)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(C_102,u1_struct_0(A_103))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103)
      | r1_tarski(k3_orders_2(A_103,D_101,C_102),C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(k3_orders_2(A_103,D_101,C_102),k1_zfmisc_1(u1_struct_0(A_103))) ) ),
    inference(resolution,[status(thm)],[c_6,c_137])).

tff(c_309,plain,(
    ! [D_153] :
      ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_153,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_153,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski(k3_orders_2('#skF_2',D_153,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_153,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_312,plain,(
    ! [D_153] :
      ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_153,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
      | ~ m1_subset_1(D_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski(k3_orders_2('#skF_2',D_153,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_153,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_309])).

tff(c_321,plain,(
    ! [D_156] :
      ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_156,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
      | ~ m1_subset_1(D_156,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski(k3_orders_2('#skF_2',D_156,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_156,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_312])).

tff(c_325,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_141,c_321])).

tff(c_328,plain,
    ( v2_struct_0('#skF_2')
    | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_34,c_32,c_30,c_28,c_26,c_22,c_325])).

tff(c_329,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_36,c_328])).

tff(c_332,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_329])).

tff(c_335,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_22,c_26,c_332])).

tff(c_337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.39  
% 2.95/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.39  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.95/1.39  
% 2.95/1.39  %Foreground sorts:
% 2.95/1.39  
% 2.95/1.39  
% 2.95/1.39  %Background operators:
% 2.95/1.39  
% 2.95/1.39  
% 2.95/1.39  %Foreground operators:
% 2.95/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.95/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.95/1.39  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.95/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.39  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.95/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.95/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.95/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.39  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.95/1.39  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.95/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.39  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.95/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.40  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.95/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.95/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.40  
% 2.95/1.41  tff(f_128, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_orders_2(A, B, C) => r1_tarski(k3_orders_2(A, D, B), k3_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_orders_2)).
% 2.95/1.41  tff(f_56, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 2.95/1.41  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 2.95/1.41  tff(f_103, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 2.95/1.41  tff(f_77, axiom, (![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_orders_2(A, B, C) & r2_orders_2(A, C, D)) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_orders_2)).
% 2.95/1.41  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.95/1.41  tff(c_34, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.95/1.41  tff(c_32, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.95/1.41  tff(c_30, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.95/1.41  tff(c_28, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.95/1.41  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.95/1.41  tff(c_26, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.95/1.41  tff(c_8, plain, (![A_8, B_9, C_10]: (m1_subset_1(k3_orders_2(A_8, B_9, C_10), k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(C_10, u1_struct_0(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_orders_2(A_8) | ~v5_orders_2(A_8) | ~v4_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.95/1.41  tff(c_18, plain, (~r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.95/1.41  tff(c_24, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.95/1.41  tff(c_6, plain, (![A_1, B_2, C_6]: (m1_subset_1('#skF_1'(A_1, B_2, C_6), A_1) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.95/1.41  tff(c_4, plain, (![A_1, B_2, C_6]: (r2_hidden('#skF_1'(A_1, B_2, C_6), B_2) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.95/1.41  tff(c_87, plain, (![A_83, B_84, C_85, D_86]: (r2_orders_2(A_83, B_84, C_85) | ~r2_hidden(B_84, k3_orders_2(A_83, D_86, C_85)) | ~m1_subset_1(D_86, k1_zfmisc_1(u1_struct_0(A_83))) | ~m1_subset_1(C_85, u1_struct_0(A_83)) | ~m1_subset_1(B_84, u1_struct_0(A_83)) | ~l1_orders_2(A_83) | ~v5_orders_2(A_83) | ~v4_orders_2(A_83) | ~v3_orders_2(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.95/1.41  tff(c_189, plain, (![A_134, A_133, C_130, D_132, C_131]: (r2_orders_2(A_134, '#skF_1'(A_133, k3_orders_2(A_134, D_132, C_130), C_131), C_130) | ~m1_subset_1(D_132, k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_subset_1(C_130, u1_struct_0(A_134)) | ~m1_subset_1('#skF_1'(A_133, k3_orders_2(A_134, D_132, C_130), C_131), u1_struct_0(A_134)) | ~l1_orders_2(A_134) | ~v5_orders_2(A_134) | ~v4_orders_2(A_134) | ~v3_orders_2(A_134) | v2_struct_0(A_134) | r1_tarski(k3_orders_2(A_134, D_132, C_130), C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(A_133)) | ~m1_subset_1(k3_orders_2(A_134, D_132, C_130), k1_zfmisc_1(A_133)))), inference(resolution, [status(thm)], [c_4, c_87])).
% 2.95/1.41  tff(c_194, plain, (![A_135, D_136, C_137, C_138]: (r2_orders_2(A_135, '#skF_1'(u1_struct_0(A_135), k3_orders_2(A_135, D_136, C_137), C_138), C_137) | ~m1_subset_1(D_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_subset_1(C_137, u1_struct_0(A_135)) | ~l1_orders_2(A_135) | ~v5_orders_2(A_135) | ~v4_orders_2(A_135) | ~v3_orders_2(A_135) | v2_struct_0(A_135) | r1_tarski(k3_orders_2(A_135, D_136, C_137), C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_subset_1(k3_orders_2(A_135, D_136, C_137), k1_zfmisc_1(u1_struct_0(A_135))))), inference(resolution, [status(thm)], [c_6, c_189])).
% 2.95/1.41  tff(c_20, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.95/1.41  tff(c_59, plain, (![A_72, B_73, D_74, C_75]: (r2_orders_2(A_72, B_73, D_74) | ~r2_orders_2(A_72, C_75, D_74) | ~r2_orders_2(A_72, B_73, C_75) | ~m1_subset_1(D_74, u1_struct_0(A_72)) | ~m1_subset_1(C_75, u1_struct_0(A_72)) | ~m1_subset_1(B_73, u1_struct_0(A_72)) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.95/1.41  tff(c_61, plain, (![B_73]: (r2_orders_2('#skF_2', B_73, '#skF_4') | ~r2_orders_2('#skF_2', B_73, '#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_73, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_59])).
% 2.95/1.41  tff(c_65, plain, (![B_76]: (r2_orders_2('#skF_2', B_76, '#skF_4') | ~r2_orders_2('#skF_2', B_76, '#skF_3') | ~m1_subset_1(B_76, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_24, c_61])).
% 2.95/1.41  tff(c_76, plain, (![B_2, C_6]: (r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2, C_6), '#skF_4') | ~r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2, C_6), '#skF_3') | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_6, c_65])).
% 2.95/1.41  tff(c_201, plain, (![D_136, C_138]: (r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_136, '#skF_3'), C_138), '#skF_4') | ~m1_subset_1(D_136, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', D_136, '#skF_3'), C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', D_136, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_194, c_76])).
% 2.95/1.41  tff(c_210, plain, (![D_136, C_138]: (r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_136, '#skF_3'), C_138), '#skF_4') | ~m1_subset_1(D_136, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', D_136, '#skF_3'), C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', D_136, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_26, c_201])).
% 2.95/1.41  tff(c_213, plain, (![D_139, C_140]: (r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_139, '#skF_3'), C_140), '#skF_4') | ~m1_subset_1(D_139, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski(k3_orders_2('#skF_2', D_139, '#skF_3'), C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', D_139, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_210])).
% 2.95/1.41  tff(c_92, plain, (![B_87, A_88, D_89, C_90]: (r2_hidden(B_87, k3_orders_2(A_88, D_89, C_90)) | ~r2_hidden(B_87, D_89) | ~r2_orders_2(A_88, B_87, C_90) | ~m1_subset_1(D_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(C_90, u1_struct_0(A_88)) | ~m1_subset_1(B_87, u1_struct_0(A_88)) | ~l1_orders_2(A_88) | ~v5_orders_2(A_88) | ~v4_orders_2(A_88) | ~v3_orders_2(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.95/1.41  tff(c_99, plain, (![B_87, C_90]: (r2_hidden(B_87, k3_orders_2('#skF_2', '#skF_5', C_90)) | ~r2_hidden(B_87, '#skF_5') | ~r2_orders_2('#skF_2', B_87, C_90) | ~m1_subset_1(C_90, u1_struct_0('#skF_2')) | ~m1_subset_1(B_87, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_92])).
% 2.95/1.41  tff(c_104, plain, (![B_87, C_90]: (r2_hidden(B_87, k3_orders_2('#skF_2', '#skF_5', C_90)) | ~r2_hidden(B_87, '#skF_5') | ~r2_orders_2('#skF_2', B_87, C_90) | ~m1_subset_1(C_90, u1_struct_0('#skF_2')) | ~m1_subset_1(B_87, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_99])).
% 2.95/1.41  tff(c_106, plain, (![B_91, C_92]: (r2_hidden(B_91, k3_orders_2('#skF_2', '#skF_5', C_92)) | ~r2_hidden(B_91, '#skF_5') | ~r2_orders_2('#skF_2', B_91, C_92) | ~m1_subset_1(C_92, u1_struct_0('#skF_2')) | ~m1_subset_1(B_91, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_104])).
% 2.95/1.41  tff(c_2, plain, (![A_1, B_2, C_6]: (~r2_hidden('#skF_1'(A_1, B_2, C_6), C_6) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.95/1.41  tff(c_123, plain, (![B_2, C_92, A_1]: (r1_tarski(B_2, k3_orders_2('#skF_2', '#skF_5', C_92)) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_92), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)) | ~r2_hidden('#skF_1'(A_1, B_2, k3_orders_2('#skF_2', '#skF_5', C_92)), '#skF_5') | ~r2_orders_2('#skF_2', '#skF_1'(A_1, B_2, k3_orders_2('#skF_2', '#skF_5', C_92)), C_92) | ~m1_subset_1(C_92, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_1, B_2, k3_orders_2('#skF_2', '#skF_5', C_92)), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_106, c_2])).
% 2.95/1.41  tff(c_216, plain, (![D_139]: (~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_139, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_139, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_subset_1(D_139, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski(k3_orders_2('#skF_2', D_139, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', D_139, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_213, c_123])).
% 2.95/1.41  tff(c_221, plain, (![D_139]: (~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_139, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_139, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_subset_1(D_139, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski(k3_orders_2('#skF_2', D_139, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', D_139, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_216])).
% 2.95/1.41  tff(c_233, plain, (~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_221])).
% 2.95/1.41  tff(c_236, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_233])).
% 2.95/1.41  tff(c_239, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_22, c_24, c_236])).
% 2.95/1.41  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_239])).
% 2.95/1.41  tff(c_243, plain, (m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_221])).
% 2.95/1.41  tff(c_82, plain, (![B_79, D_80, A_81, C_82]: (r2_hidden(B_79, D_80) | ~r2_hidden(B_79, k3_orders_2(A_81, D_80, C_82)) | ~m1_subset_1(D_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~m1_subset_1(C_82, u1_struct_0(A_81)) | ~m1_subset_1(B_79, u1_struct_0(A_81)) | ~l1_orders_2(A_81) | ~v5_orders_2(A_81) | ~v4_orders_2(A_81) | ~v3_orders_2(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.95/1.41  tff(c_137, plain, (![C_104, C_102, A_105, D_101, A_103]: (r2_hidden('#skF_1'(A_105, k3_orders_2(A_103, D_101, C_102), C_104), D_101) | ~m1_subset_1(D_101, k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(C_102, u1_struct_0(A_103)) | ~m1_subset_1('#skF_1'(A_105, k3_orders_2(A_103, D_101, C_102), C_104), u1_struct_0(A_103)) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103) | r1_tarski(k3_orders_2(A_103, D_101, C_102), C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(A_105)) | ~m1_subset_1(k3_orders_2(A_103, D_101, C_102), k1_zfmisc_1(A_105)))), inference(resolution, [status(thm)], [c_4, c_82])).
% 2.95/1.41  tff(c_141, plain, (![A_103, D_101, C_102, C_6]: (r2_hidden('#skF_1'(u1_struct_0(A_103), k3_orders_2(A_103, D_101, C_102), C_6), D_101) | ~m1_subset_1(D_101, k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(C_102, u1_struct_0(A_103)) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103) | r1_tarski(k3_orders_2(A_103, D_101, C_102), C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(k3_orders_2(A_103, D_101, C_102), k1_zfmisc_1(u1_struct_0(A_103))))), inference(resolution, [status(thm)], [c_6, c_137])).
% 2.95/1.41  tff(c_309, plain, (![D_153]: (~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_153, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_153, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_subset_1(D_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski(k3_orders_2('#skF_2', D_153, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', D_153, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_221])).
% 2.95/1.41  tff(c_312, plain, (![D_153]: (~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_153, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | ~m1_subset_1(D_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski(k3_orders_2('#skF_2', D_153, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', D_153, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_6, c_309])).
% 2.95/1.41  tff(c_321, plain, (![D_156]: (~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_156, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | ~m1_subset_1(D_156, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski(k3_orders_2('#skF_2', D_156, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', D_156, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_312])).
% 2.95/1.41  tff(c_325, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_141, c_321])).
% 2.95/1.41  tff(c_328, plain, (v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_34, c_32, c_30, c_28, c_26, c_22, c_325])).
% 2.95/1.41  tff(c_329, plain, (~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_18, c_36, c_328])).
% 2.95/1.41  tff(c_332, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_329])).
% 2.95/1.41  tff(c_335, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_22, c_26, c_332])).
% 2.95/1.41  tff(c_337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_335])).
% 2.95/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.41  
% 2.95/1.41  Inference rules
% 2.95/1.41  ----------------------
% 2.95/1.41  #Ref     : 0
% 2.95/1.41  #Sup     : 54
% 2.95/1.42  #Fact    : 0
% 2.95/1.42  #Define  : 0
% 2.95/1.42  #Split   : 2
% 2.95/1.42  #Chain   : 0
% 2.95/1.42  #Close   : 0
% 2.95/1.42  
% 2.95/1.42  Ordering : KBO
% 2.95/1.42  
% 2.95/1.42  Simplification rules
% 2.95/1.42  ----------------------
% 2.95/1.42  #Subsume      : 2
% 2.95/1.42  #Demod        : 90
% 2.95/1.42  #Tautology    : 9
% 2.95/1.42  #SimpNegUnit  : 16
% 2.95/1.42  #BackRed      : 0
% 2.95/1.42  
% 2.95/1.42  #Partial instantiations: 0
% 2.95/1.42  #Strategies tried      : 1
% 2.95/1.42  
% 2.95/1.42  Timing (in seconds)
% 2.95/1.42  ----------------------
% 2.95/1.42  Preprocessing        : 0.31
% 2.95/1.42  Parsing              : 0.18
% 2.95/1.42  CNF conversion       : 0.03
% 2.95/1.42  Main loop            : 0.34
% 2.95/1.42  Inferencing          : 0.14
% 2.95/1.42  Reduction            : 0.08
% 2.95/1.42  Demodulation         : 0.06
% 2.95/1.42  BG Simplification    : 0.02
% 2.95/1.42  Subsumption          : 0.08
% 2.95/1.42  Abstraction          : 0.01
% 2.95/1.42  MUC search           : 0.00
% 2.95/1.42  Cooper               : 0.00
% 2.95/1.42  Total                : 0.69
% 2.95/1.42  Index Insertion      : 0.00
% 2.95/1.42  Index Deletion       : 0.00
% 2.95/1.42  Index Matching       : 0.00
% 2.95/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
