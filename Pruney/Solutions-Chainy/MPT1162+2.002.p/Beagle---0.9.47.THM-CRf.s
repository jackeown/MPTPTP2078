%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:47 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 343 expanded)
%              Number of leaves         :   27 ( 147 expanded)
%              Depth                    :   20
%              Number of atoms          :  350 (1909 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

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

tff(f_147,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_orders_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_96,axiom,(
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
                 => ( ( ( r2_orders_2(A,B,C)
                        & r1_orders_2(A,C,D) )
                      | ( r1_orders_2(A,B,C)
                        & r2_orders_2(A,C,D) ) )
                   => r2_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).

tff(f_122,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_42,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_40,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_38,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_36,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_14,plain,(
    ! [A_15,B_16,C_17] :
      ( m1_subset_1(k3_orders_2(A_15,B_16,C_17),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(C_17,u1_struct_0(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_orders_2(A_15)
      | ~ v5_orders_2(A_15)
      | ~ v4_orders_2(A_15)
      | ~ v3_orders_2(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ~ r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_6,plain,(
    ! [A_1,B_2,C_6] :
      ( m1_subset_1('#skF_1'(A_1,B_2,C_6),A_1)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_121,plain,(
    ! [A_86,C_87,D_88,B_89] :
      ( ~ r2_orders_2(A_86,C_87,D_88)
      | ~ r1_orders_2(A_86,B_89,C_87)
      | r2_orders_2(A_86,B_89,D_88)
      | ~ m1_subset_1(D_88,u1_struct_0(A_86))
      | ~ m1_subset_1(C_87,u1_struct_0(A_86))
      | ~ m1_subset_1(B_89,u1_struct_0(A_86))
      | ~ l1_orders_2(A_86)
      | ~ v5_orders_2(A_86)
      | ~ v4_orders_2(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_123,plain,(
    ! [B_89] :
      ( ~ r1_orders_2('#skF_2',B_89,'#skF_3')
      | r2_orders_2('#skF_2',B_89,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_89,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_121])).

tff(c_127,plain,(
    ! [B_90] :
      ( ~ r1_orders_2('#skF_2',B_90,'#skF_3')
      | r2_orders_2('#skF_2',B_90,'#skF_4')
      | ~ m1_subset_1(B_90,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_123])).

tff(c_138,plain,(
    ! [B_2,C_6] :
      ( ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2,C_6),'#skF_3')
      | r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2,C_6),'#skF_4')
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_127])).

tff(c_213,plain,(
    ! [B_115,A_116,D_117,C_118] :
      ( r2_hidden(B_115,k3_orders_2(A_116,D_117,C_118))
      | ~ r2_hidden(B_115,D_117)
      | ~ r2_orders_2(A_116,B_115,C_118)
      | ~ m1_subset_1(D_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ m1_subset_1(C_118,u1_struct_0(A_116))
      | ~ m1_subset_1(B_115,u1_struct_0(A_116))
      | ~ l1_orders_2(A_116)
      | ~ v5_orders_2(A_116)
      | ~ v4_orders_2(A_116)
      | ~ v3_orders_2(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_220,plain,(
    ! [B_115,C_118] :
      ( r2_hidden(B_115,k3_orders_2('#skF_2','#skF_5',C_118))
      | ~ r2_hidden(B_115,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_115,C_118)
      | ~ m1_subset_1(C_118,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_115,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_213])).

tff(c_225,plain,(
    ! [B_115,C_118] :
      ( r2_hidden(B_115,k3_orders_2('#skF_2','#skF_5',C_118))
      | ~ r2_hidden(B_115,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_115,C_118)
      | ~ m1_subset_1(C_118,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_115,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_220])).

tff(c_227,plain,(
    ! [B_119,C_120] :
      ( r2_hidden(B_119,k3_orders_2('#skF_2','#skF_5',C_120))
      | ~ r2_hidden(B_119,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_119,C_120)
      | ~ m1_subset_1(C_120,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_225])).

tff(c_2,plain,(
    ! [A_1,B_2,C_6] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_6),C_6)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_317,plain,(
    ! [B_161,C_162,A_163] :
      ( r1_tarski(B_161,k3_orders_2('#skF_2','#skF_5',C_162))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_162),k1_zfmisc_1(A_163))
      | ~ m1_subset_1(B_161,k1_zfmisc_1(A_163))
      | ~ r2_hidden('#skF_1'(A_163,B_161,k3_orders_2('#skF_2','#skF_5',C_162)),'#skF_5')
      | ~ r2_orders_2('#skF_2','#skF_1'(A_163,B_161,k3_orders_2('#skF_2','#skF_5',C_162)),C_162)
      | ~ m1_subset_1(C_162,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_163,B_161,k3_orders_2('#skF_2','#skF_5',C_162)),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_227,c_2])).

tff(c_329,plain,(
    ! [B_2] :
      ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_2,k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_2,k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2'))
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2,k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_3')
      | r1_tarski(B_2,k3_orders_2('#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_138,c_317])).

tff(c_341,plain,(
    ! [B_2] :
      ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_2,k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_2,k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2'))
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2,k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_3')
      | r1_tarski(B_2,k3_orders_2('#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_329])).

tff(c_414,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_417,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_414])).

tff(c_420,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_30,c_32,c_417])).

tff(c_422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_420])).

tff(c_424,plain,(
    m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_4,plain,(
    ! [A_1,B_2,C_6] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_6),B_2)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_192,plain,(
    ! [B_105,D_106,A_107,C_108] :
      ( r2_hidden(B_105,D_106)
      | ~ r2_hidden(B_105,k3_orders_2(A_107,D_106,C_108))
      | ~ m1_subset_1(D_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_subset_1(C_108,u1_struct_0(A_107))
      | ~ m1_subset_1(B_105,u1_struct_0(A_107))
      | ~ l1_orders_2(A_107)
      | ~ v5_orders_2(A_107)
      | ~ v4_orders_2(A_107)
      | ~ v3_orders_2(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_277,plain,(
    ! [A_141,D_137,C_139,C_138,A_140] :
      ( r2_hidden('#skF_1'(A_140,k3_orders_2(A_141,D_137,C_138),C_139),D_137)
      | ~ m1_subset_1(D_137,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ m1_subset_1(C_138,u1_struct_0(A_141))
      | ~ m1_subset_1('#skF_1'(A_140,k3_orders_2(A_141,D_137,C_138),C_139),u1_struct_0(A_141))
      | ~ l1_orders_2(A_141)
      | ~ v5_orders_2(A_141)
      | ~ v4_orders_2(A_141)
      | ~ v3_orders_2(A_141)
      | v2_struct_0(A_141)
      | r1_tarski(k3_orders_2(A_141,D_137,C_138),C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(A_140))
      | ~ m1_subset_1(k3_orders_2(A_141,D_137,C_138),k1_zfmisc_1(A_140)) ) ),
    inference(resolution,[status(thm)],[c_4,c_192])).

tff(c_281,plain,(
    ! [A_141,D_137,C_138,C_6] :
      ( r2_hidden('#skF_1'(u1_struct_0(A_141),k3_orders_2(A_141,D_137,C_138),C_6),D_137)
      | ~ m1_subset_1(D_137,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ m1_subset_1(C_138,u1_struct_0(A_141))
      | ~ l1_orders_2(A_141)
      | ~ v5_orders_2(A_141)
      | ~ v4_orders_2(A_141)
      | ~ v3_orders_2(A_141)
      | v2_struct_0(A_141)
      | r1_tarski(k3_orders_2(A_141,D_137,C_138),C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ m1_subset_1(k3_orders_2(A_141,D_137,C_138),k1_zfmisc_1(u1_struct_0(A_141))) ) ),
    inference(resolution,[status(thm)],[c_6,c_277])).

tff(c_197,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( r2_orders_2(A_109,B_110,C_111)
      | ~ r2_hidden(B_110,k3_orders_2(A_109,D_112,C_111))
      | ~ m1_subset_1(D_112,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_subset_1(C_111,u1_struct_0(A_109))
      | ~ m1_subset_1(B_110,u1_struct_0(A_109))
      | ~ l1_orders_2(A_109)
      | ~ v5_orders_2(A_109)
      | ~ v4_orders_2(A_109)
      | ~ v3_orders_2(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_344,plain,(
    ! [C_170,D_172,A_171,C_174,A_173] :
      ( r2_orders_2(A_171,'#skF_1'(A_173,k3_orders_2(A_171,D_172,C_174),C_170),C_174)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ m1_subset_1(C_174,u1_struct_0(A_171))
      | ~ m1_subset_1('#skF_1'(A_173,k3_orders_2(A_171,D_172,C_174),C_170),u1_struct_0(A_171))
      | ~ l1_orders_2(A_171)
      | ~ v5_orders_2(A_171)
      | ~ v4_orders_2(A_171)
      | ~ v3_orders_2(A_171)
      | v2_struct_0(A_171)
      | r1_tarski(k3_orders_2(A_171,D_172,C_174),C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(A_173))
      | ~ m1_subset_1(k3_orders_2(A_171,D_172,C_174),k1_zfmisc_1(A_173)) ) ),
    inference(resolution,[status(thm)],[c_4,c_197])).

tff(c_349,plain,(
    ! [A_175,D_176,C_177,C_178] :
      ( r2_orders_2(A_175,'#skF_1'(u1_struct_0(A_175),k3_orders_2(A_175,D_176,C_177),C_178),C_177)
      | ~ m1_subset_1(D_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ m1_subset_1(C_177,u1_struct_0(A_175))
      | ~ l1_orders_2(A_175)
      | ~ v5_orders_2(A_175)
      | ~ v4_orders_2(A_175)
      | ~ v3_orders_2(A_175)
      | v2_struct_0(A_175)
      | r1_tarski(k3_orders_2(A_175,D_176,C_177),C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ m1_subset_1(k3_orders_2(A_175,D_176,C_177),k1_zfmisc_1(u1_struct_0(A_175))) ) ),
    inference(resolution,[status(thm)],[c_6,c_344])).

tff(c_62,plain,(
    ! [A_72,B_73,C_74] :
      ( r1_orders_2(A_72,B_73,C_74)
      | ~ r2_orders_2(A_72,B_73,C_74)
      | ~ m1_subset_1(C_74,u1_struct_0(A_72))
      | ~ m1_subset_1(B_73,u1_struct_0(A_72))
      | ~ l1_orders_2(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_64,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_62])).

tff(c_67,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_64])).

tff(c_165,plain,(
    ! [A_98,C_99,D_100,B_101] :
      ( ~ r1_orders_2(A_98,C_99,D_100)
      | ~ r2_orders_2(A_98,B_101,C_99)
      | r2_orders_2(A_98,B_101,D_100)
      | ~ m1_subset_1(D_100,u1_struct_0(A_98))
      | ~ m1_subset_1(C_99,u1_struct_0(A_98))
      | ~ m1_subset_1(B_101,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v4_orders_2(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_167,plain,(
    ! [B_101] :
      ( ~ r2_orders_2('#skF_2',B_101,'#skF_3')
      | r2_orders_2('#skF_2',B_101,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_101,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_67,c_165])).

tff(c_171,plain,(
    ! [B_102] :
      ( ~ r2_orders_2('#skF_2',B_102,'#skF_3')
      | r2_orders_2('#skF_2',B_102,'#skF_4')
      | ~ m1_subset_1(B_102,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_167])).

tff(c_182,plain,(
    ! [B_2,C_6] :
      ( ~ r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2,C_6),'#skF_3')
      | r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2,C_6),'#skF_4')
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_171])).

tff(c_356,plain,(
    ! [D_176,C_178] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_176,'#skF_3'),C_178),'#skF_4')
      | ~ m1_subset_1(D_176,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2',D_176,'#skF_3'),C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_176,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_349,c_182])).

tff(c_367,plain,(
    ! [D_176,C_178] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_176,'#skF_3'),C_178),'#skF_4')
      | ~ m1_subset_1(D_176,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2',D_176,'#skF_3'),C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_176,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_356])).

tff(c_371,plain,(
    ! [D_179,C_180] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_179,'#skF_3'),C_180),'#skF_4')
      | ~ m1_subset_1(D_179,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski(k3_orders_2('#skF_2',D_179,'#skF_3'),C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_179,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_367])).

tff(c_244,plain,(
    ! [B_2,C_120,A_1] :
      ( r1_tarski(B_2,k3_orders_2('#skF_2','#skF_5',C_120))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5',C_120),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1))
      | ~ r2_hidden('#skF_1'(A_1,B_2,k3_orders_2('#skF_2','#skF_5',C_120)),'#skF_5')
      | ~ r2_orders_2('#skF_2','#skF_1'(A_1,B_2,k3_orders_2('#skF_2','#skF_5',C_120)),C_120)
      | ~ m1_subset_1(C_120,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_1,B_2,k3_orders_2('#skF_2','#skF_5',C_120)),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_227,c_2])).

tff(c_374,plain,(
    ! [D_179] :
      ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_179,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_179,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_179,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski(k3_orders_2('#skF_2',D_179,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_179,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_371,c_244])).

tff(c_381,plain,(
    ! [D_179] :
      ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_179,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_179,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_179,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski(k3_orders_2('#skF_2',D_179,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_179,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_374])).

tff(c_512,plain,(
    ! [D_208] :
      ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_208,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_208,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_208,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski(k3_orders_2('#skF_2',D_208,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_208,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_381])).

tff(c_515,plain,(
    ! [D_208] :
      ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_208,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
      | ~ m1_subset_1(D_208,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski(k3_orders_2('#skF_2',D_208,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_208,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_512])).

tff(c_530,plain,(
    ! [D_214] :
      ( ~ r2_hidden('#skF_1'(u1_struct_0('#skF_2'),k3_orders_2('#skF_2',D_214,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
      | ~ m1_subset_1(D_214,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski(k3_orders_2('#skF_2',D_214,'#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(k3_orders_2('#skF_2',D_214,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_515])).

tff(c_534,plain,
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
    inference(resolution,[status(thm)],[c_281,c_530])).

tff(c_537,plain,
    ( v2_struct_0('#skF_2')
    | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_42,c_40,c_38,c_36,c_34,c_30,c_534])).

tff(c_538,plain,(
    ~ m1_subset_1(k3_orders_2('#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_44,c_537])).

tff(c_541,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_538])).

tff(c_544,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_30,c_34,c_541])).

tff(c_546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_544])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:23:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.56  
% 3.62/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.56  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.62/1.56  
% 3.62/1.56  %Foreground sorts:
% 3.62/1.56  
% 3.62/1.56  
% 3.62/1.56  %Background operators:
% 3.62/1.56  
% 3.62/1.56  
% 3.62/1.56  %Foreground operators:
% 3.62/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.62/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.62/1.56  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.62/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.56  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.62/1.56  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.62/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.62/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.62/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.62/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.62/1.56  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.62/1.56  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.62/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.56  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.62/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.62/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.56  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.62/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.62/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.56  
% 3.62/1.60  tff(f_147, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_orders_2(A, B, C) => r1_tarski(k3_orders_2(A, D, B), k3_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_orders_2)).
% 3.62/1.60  tff(f_71, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 3.62/1.60  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 3.62/1.60  tff(f_96, axiom, (![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((r2_orders_2(A, B, C) & r1_orders_2(A, C, D)) | (r1_orders_2(A, B, C) & r2_orders_2(A, C, D))) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_orders_2)).
% 3.62/1.60  tff(f_122, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 3.62/1.60  tff(f_54, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 3.62/1.60  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.60  tff(c_42, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.60  tff(c_40, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.60  tff(c_38, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.60  tff(c_36, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.60  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.60  tff(c_34, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.60  tff(c_14, plain, (![A_15, B_16, C_17]: (m1_subset_1(k3_orders_2(A_15, B_16, C_17), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(C_17, u1_struct_0(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_orders_2(A_15) | ~v5_orders_2(A_15) | ~v4_orders_2(A_15) | ~v3_orders_2(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.62/1.60  tff(c_26, plain, (~r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.60  tff(c_32, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.60  tff(c_6, plain, (![A_1, B_2, C_6]: (m1_subset_1('#skF_1'(A_1, B_2, C_6), A_1) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.62/1.60  tff(c_28, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.60  tff(c_121, plain, (![A_86, C_87, D_88, B_89]: (~r2_orders_2(A_86, C_87, D_88) | ~r1_orders_2(A_86, B_89, C_87) | r2_orders_2(A_86, B_89, D_88) | ~m1_subset_1(D_88, u1_struct_0(A_86)) | ~m1_subset_1(C_87, u1_struct_0(A_86)) | ~m1_subset_1(B_89, u1_struct_0(A_86)) | ~l1_orders_2(A_86) | ~v5_orders_2(A_86) | ~v4_orders_2(A_86))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.62/1.60  tff(c_123, plain, (![B_89]: (~r1_orders_2('#skF_2', B_89, '#skF_3') | r2_orders_2('#skF_2', B_89, '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_89, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_121])).
% 3.62/1.60  tff(c_127, plain, (![B_90]: (~r1_orders_2('#skF_2', B_90, '#skF_3') | r2_orders_2('#skF_2', B_90, '#skF_4') | ~m1_subset_1(B_90, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_123])).
% 3.62/1.60  tff(c_138, plain, (![B_2, C_6]: (~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2, C_6), '#skF_3') | r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2, C_6), '#skF_4') | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_6, c_127])).
% 3.62/1.60  tff(c_213, plain, (![B_115, A_116, D_117, C_118]: (r2_hidden(B_115, k3_orders_2(A_116, D_117, C_118)) | ~r2_hidden(B_115, D_117) | ~r2_orders_2(A_116, B_115, C_118) | ~m1_subset_1(D_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~m1_subset_1(C_118, u1_struct_0(A_116)) | ~m1_subset_1(B_115, u1_struct_0(A_116)) | ~l1_orders_2(A_116) | ~v5_orders_2(A_116) | ~v4_orders_2(A_116) | ~v3_orders_2(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.62/1.60  tff(c_220, plain, (![B_115, C_118]: (r2_hidden(B_115, k3_orders_2('#skF_2', '#skF_5', C_118)) | ~r2_hidden(B_115, '#skF_5') | ~r2_orders_2('#skF_2', B_115, C_118) | ~m1_subset_1(C_118, u1_struct_0('#skF_2')) | ~m1_subset_1(B_115, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_213])).
% 3.62/1.60  tff(c_225, plain, (![B_115, C_118]: (r2_hidden(B_115, k3_orders_2('#skF_2', '#skF_5', C_118)) | ~r2_hidden(B_115, '#skF_5') | ~r2_orders_2('#skF_2', B_115, C_118) | ~m1_subset_1(C_118, u1_struct_0('#skF_2')) | ~m1_subset_1(B_115, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_220])).
% 3.62/1.60  tff(c_227, plain, (![B_119, C_120]: (r2_hidden(B_119, k3_orders_2('#skF_2', '#skF_5', C_120)) | ~r2_hidden(B_119, '#skF_5') | ~r2_orders_2('#skF_2', B_119, C_120) | ~m1_subset_1(C_120, u1_struct_0('#skF_2')) | ~m1_subset_1(B_119, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_225])).
% 3.62/1.60  tff(c_2, plain, (![A_1, B_2, C_6]: (~r2_hidden('#skF_1'(A_1, B_2, C_6), C_6) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.62/1.60  tff(c_317, plain, (![B_161, C_162, A_163]: (r1_tarski(B_161, k3_orders_2('#skF_2', '#skF_5', C_162)) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_162), k1_zfmisc_1(A_163)) | ~m1_subset_1(B_161, k1_zfmisc_1(A_163)) | ~r2_hidden('#skF_1'(A_163, B_161, k3_orders_2('#skF_2', '#skF_5', C_162)), '#skF_5') | ~r2_orders_2('#skF_2', '#skF_1'(A_163, B_161, k3_orders_2('#skF_2', '#skF_5', C_162)), C_162) | ~m1_subset_1(C_162, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_163, B_161, k3_orders_2('#skF_2', '#skF_5', C_162)), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_227, c_2])).
% 3.62/1.60  tff(c_329, plain, (![B_2]: (~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_2, k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_2, k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2')) | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2, k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_3') | r1_tarski(B_2, k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_138, c_317])).
% 3.62/1.60  tff(c_341, plain, (![B_2]: (~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_2, k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_2, k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2')) | ~r1_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2, k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_3') | r1_tarski(B_2, k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_329])).
% 3.62/1.60  tff(c_414, plain, (~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_341])).
% 3.62/1.60  tff(c_417, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_414])).
% 3.62/1.60  tff(c_420, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_30, c_32, c_417])).
% 3.62/1.60  tff(c_422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_420])).
% 3.62/1.60  tff(c_424, plain, (m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_341])).
% 3.62/1.60  tff(c_4, plain, (![A_1, B_2, C_6]: (r2_hidden('#skF_1'(A_1, B_2, C_6), B_2) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.62/1.60  tff(c_192, plain, (![B_105, D_106, A_107, C_108]: (r2_hidden(B_105, D_106) | ~r2_hidden(B_105, k3_orders_2(A_107, D_106, C_108)) | ~m1_subset_1(D_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~m1_subset_1(C_108, u1_struct_0(A_107)) | ~m1_subset_1(B_105, u1_struct_0(A_107)) | ~l1_orders_2(A_107) | ~v5_orders_2(A_107) | ~v4_orders_2(A_107) | ~v3_orders_2(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.62/1.60  tff(c_277, plain, (![A_141, D_137, C_139, C_138, A_140]: (r2_hidden('#skF_1'(A_140, k3_orders_2(A_141, D_137, C_138), C_139), D_137) | ~m1_subset_1(D_137, k1_zfmisc_1(u1_struct_0(A_141))) | ~m1_subset_1(C_138, u1_struct_0(A_141)) | ~m1_subset_1('#skF_1'(A_140, k3_orders_2(A_141, D_137, C_138), C_139), u1_struct_0(A_141)) | ~l1_orders_2(A_141) | ~v5_orders_2(A_141) | ~v4_orders_2(A_141) | ~v3_orders_2(A_141) | v2_struct_0(A_141) | r1_tarski(k3_orders_2(A_141, D_137, C_138), C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(A_140)) | ~m1_subset_1(k3_orders_2(A_141, D_137, C_138), k1_zfmisc_1(A_140)))), inference(resolution, [status(thm)], [c_4, c_192])).
% 3.62/1.60  tff(c_281, plain, (![A_141, D_137, C_138, C_6]: (r2_hidden('#skF_1'(u1_struct_0(A_141), k3_orders_2(A_141, D_137, C_138), C_6), D_137) | ~m1_subset_1(D_137, k1_zfmisc_1(u1_struct_0(A_141))) | ~m1_subset_1(C_138, u1_struct_0(A_141)) | ~l1_orders_2(A_141) | ~v5_orders_2(A_141) | ~v4_orders_2(A_141) | ~v3_orders_2(A_141) | v2_struct_0(A_141) | r1_tarski(k3_orders_2(A_141, D_137, C_138), C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(u1_struct_0(A_141))) | ~m1_subset_1(k3_orders_2(A_141, D_137, C_138), k1_zfmisc_1(u1_struct_0(A_141))))), inference(resolution, [status(thm)], [c_6, c_277])).
% 3.62/1.60  tff(c_197, plain, (![A_109, B_110, C_111, D_112]: (r2_orders_2(A_109, B_110, C_111) | ~r2_hidden(B_110, k3_orders_2(A_109, D_112, C_111)) | ~m1_subset_1(D_112, k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_subset_1(C_111, u1_struct_0(A_109)) | ~m1_subset_1(B_110, u1_struct_0(A_109)) | ~l1_orders_2(A_109) | ~v5_orders_2(A_109) | ~v4_orders_2(A_109) | ~v3_orders_2(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.62/1.60  tff(c_344, plain, (![C_170, D_172, A_171, C_174, A_173]: (r2_orders_2(A_171, '#skF_1'(A_173, k3_orders_2(A_171, D_172, C_174), C_170), C_174) | ~m1_subset_1(D_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~m1_subset_1(C_174, u1_struct_0(A_171)) | ~m1_subset_1('#skF_1'(A_173, k3_orders_2(A_171, D_172, C_174), C_170), u1_struct_0(A_171)) | ~l1_orders_2(A_171) | ~v5_orders_2(A_171) | ~v4_orders_2(A_171) | ~v3_orders_2(A_171) | v2_struct_0(A_171) | r1_tarski(k3_orders_2(A_171, D_172, C_174), C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(A_173)) | ~m1_subset_1(k3_orders_2(A_171, D_172, C_174), k1_zfmisc_1(A_173)))), inference(resolution, [status(thm)], [c_4, c_197])).
% 3.62/1.60  tff(c_349, plain, (![A_175, D_176, C_177, C_178]: (r2_orders_2(A_175, '#skF_1'(u1_struct_0(A_175), k3_orders_2(A_175, D_176, C_177), C_178), C_177) | ~m1_subset_1(D_176, k1_zfmisc_1(u1_struct_0(A_175))) | ~m1_subset_1(C_177, u1_struct_0(A_175)) | ~l1_orders_2(A_175) | ~v5_orders_2(A_175) | ~v4_orders_2(A_175) | ~v3_orders_2(A_175) | v2_struct_0(A_175) | r1_tarski(k3_orders_2(A_175, D_176, C_177), C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(u1_struct_0(A_175))) | ~m1_subset_1(k3_orders_2(A_175, D_176, C_177), k1_zfmisc_1(u1_struct_0(A_175))))), inference(resolution, [status(thm)], [c_6, c_344])).
% 3.62/1.60  tff(c_62, plain, (![A_72, B_73, C_74]: (r1_orders_2(A_72, B_73, C_74) | ~r2_orders_2(A_72, B_73, C_74) | ~m1_subset_1(C_74, u1_struct_0(A_72)) | ~m1_subset_1(B_73, u1_struct_0(A_72)) | ~l1_orders_2(A_72))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.62/1.60  tff(c_64, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_28, c_62])).
% 3.62/1.60  tff(c_67, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_64])).
% 3.62/1.60  tff(c_165, plain, (![A_98, C_99, D_100, B_101]: (~r1_orders_2(A_98, C_99, D_100) | ~r2_orders_2(A_98, B_101, C_99) | r2_orders_2(A_98, B_101, D_100) | ~m1_subset_1(D_100, u1_struct_0(A_98)) | ~m1_subset_1(C_99, u1_struct_0(A_98)) | ~m1_subset_1(B_101, u1_struct_0(A_98)) | ~l1_orders_2(A_98) | ~v5_orders_2(A_98) | ~v4_orders_2(A_98))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.62/1.60  tff(c_167, plain, (![B_101]: (~r2_orders_2('#skF_2', B_101, '#skF_3') | r2_orders_2('#skF_2', B_101, '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_101, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_67, c_165])).
% 3.62/1.60  tff(c_171, plain, (![B_102]: (~r2_orders_2('#skF_2', B_102, '#skF_3') | r2_orders_2('#skF_2', B_102, '#skF_4') | ~m1_subset_1(B_102, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_167])).
% 3.62/1.60  tff(c_182, plain, (![B_2, C_6]: (~r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2, C_6), '#skF_3') | r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2, C_6), '#skF_4') | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_6, c_171])).
% 3.62/1.60  tff(c_356, plain, (![D_176, C_178]: (r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_176, '#skF_3'), C_178), '#skF_4') | ~m1_subset_1(D_176, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', D_176, '#skF_3'), C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', D_176, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_349, c_182])).
% 3.62/1.60  tff(c_367, plain, (![D_176, C_178]: (r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_176, '#skF_3'), C_178), '#skF_4') | ~m1_subset_1(D_176, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', D_176, '#skF_3'), C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', D_176, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_356])).
% 3.62/1.60  tff(c_371, plain, (![D_179, C_180]: (r2_orders_2('#skF_2', '#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_179, '#skF_3'), C_180), '#skF_4') | ~m1_subset_1(D_179, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski(k3_orders_2('#skF_2', D_179, '#skF_3'), C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', D_179, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_367])).
% 3.62/1.60  tff(c_244, plain, (![B_2, C_120, A_1]: (r1_tarski(B_2, k3_orders_2('#skF_2', '#skF_5', C_120)) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', C_120), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)) | ~r2_hidden('#skF_1'(A_1, B_2, k3_orders_2('#skF_2', '#skF_5', C_120)), '#skF_5') | ~r2_orders_2('#skF_2', '#skF_1'(A_1, B_2, k3_orders_2('#skF_2', '#skF_5', C_120)), C_120) | ~m1_subset_1(C_120, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_1, B_2, k3_orders_2('#skF_2', '#skF_5', C_120)), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_227, c_2])).
% 3.62/1.60  tff(c_374, plain, (![D_179]: (~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_179, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_179, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_subset_1(D_179, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski(k3_orders_2('#skF_2', D_179, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', D_179, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_371, c_244])).
% 3.62/1.60  tff(c_381, plain, (![D_179]: (~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_179, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_179, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_subset_1(D_179, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski(k3_orders_2('#skF_2', D_179, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', D_179, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_374])).
% 3.62/1.60  tff(c_512, plain, (![D_208]: (~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_208, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_208, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_subset_1(D_208, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski(k3_orders_2('#skF_2', D_208, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', D_208, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_424, c_381])).
% 3.62/1.60  tff(c_515, plain, (![D_208]: (~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_208, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | ~m1_subset_1(D_208, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski(k3_orders_2('#skF_2', D_208, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', D_208, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_6, c_512])).
% 3.62/1.60  tff(c_530, plain, (![D_214]: (~r2_hidden('#skF_1'(u1_struct_0('#skF_2'), k3_orders_2('#skF_2', D_214, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | ~m1_subset_1(D_214, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski(k3_orders_2('#skF_2', D_214, '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', D_214, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_424, c_515])).
% 3.62/1.60  tff(c_534, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_281, c_530])).
% 3.62/1.60  tff(c_537, plain, (v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_424, c_42, c_40, c_38, c_36, c_34, c_30, c_534])).
% 3.62/1.60  tff(c_538, plain, (~m1_subset_1(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_26, c_44, c_537])).
% 3.62/1.60  tff(c_541, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_538])).
% 3.62/1.60  tff(c_544, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_30, c_34, c_541])).
% 3.62/1.60  tff(c_546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_544])).
% 3.62/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.60  
% 3.62/1.60  Inference rules
% 3.62/1.60  ----------------------
% 3.62/1.60  #Ref     : 0
% 3.62/1.60  #Sup     : 89
% 3.62/1.60  #Fact    : 0
% 3.62/1.60  #Define  : 0
% 3.62/1.60  #Split   : 3
% 3.62/1.60  #Chain   : 0
% 3.62/1.60  #Close   : 0
% 3.62/1.60  
% 3.62/1.60  Ordering : KBO
% 3.62/1.60  
% 3.62/1.60  Simplification rules
% 3.62/1.60  ----------------------
% 3.62/1.60  #Subsume      : 10
% 3.62/1.60  #Demod        : 139
% 3.62/1.60  #Tautology    : 17
% 3.62/1.60  #SimpNegUnit  : 15
% 3.62/1.60  #BackRed      : 0
% 3.62/1.60  
% 3.62/1.60  #Partial instantiations: 0
% 3.62/1.60  #Strategies tried      : 1
% 3.62/1.60  
% 3.62/1.60  Timing (in seconds)
% 3.62/1.60  ----------------------
% 3.62/1.60  Preprocessing        : 0.33
% 3.62/1.60  Parsing              : 0.18
% 3.62/1.60  CNF conversion       : 0.03
% 3.62/1.60  Main loop            : 0.48
% 3.62/1.60  Inferencing          : 0.20
% 3.62/1.60  Reduction            : 0.13
% 3.62/1.60  Demodulation         : 0.09
% 3.62/1.60  BG Simplification    : 0.02
% 3.62/1.60  Subsumption          : 0.12
% 3.62/1.60  Abstraction          : 0.02
% 3.62/1.60  MUC search           : 0.00
% 3.62/1.60  Cooper               : 0.00
% 3.62/1.60  Total                : 0.87
% 3.62/1.60  Index Insertion      : 0.00
% 3.62/1.60  Index Deletion       : 0.00
% 3.62/1.60  Index Matching       : 0.00
% 3.62/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
