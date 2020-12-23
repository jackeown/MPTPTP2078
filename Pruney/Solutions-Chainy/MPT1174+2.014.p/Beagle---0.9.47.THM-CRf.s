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
% DateTime   : Thu Dec  3 10:19:54 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 329 expanded)
%              Number of leaves         :   36 ( 148 expanded)
%              Depth                    :   30
%              Number of atoms          :  364 (1705 expanded)
%              Number of equality atoms :   36 ( 235 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_186,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_orders_1(C,k1_orders_1(u1_struct_0(A)))
               => ! [D] :
                    ( m2_orders_2(D,A,C)
                   => ( B = k1_funct_1(C,u1_struct_0(A))
                     => k3_orders_2(A,D,B) = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_orders_2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_132,axiom,(
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

tff(f_161,axiom,(
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
                  ( m1_orders_1(D,k1_orders_1(u1_struct_0(A)))
                 => ! [E] :
                      ( m2_orders_2(E,A,D)
                     => ( ( r2_hidden(B,E)
                          & C = k1_funct_1(D,u1_struct_0(A)) )
                       => r3_orders_2(A,C,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_orders_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_orders_2)).

tff(c_26,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_42,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_40,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_38,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_36,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_32,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_30,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_73,plain,(
    ! [C_97,A_98,B_99] :
      ( m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m2_orders_2(C_97,A_98,B_99)
      | ~ m1_orders_1(B_99,k1_orders_1(u1_struct_0(A_98)))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v4_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_75,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_73])).

tff(c_78,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_32,c_75])).

tff(c_79,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_78])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_108,plain,(
    ! [A_104,B_105,C_106] :
      ( m1_subset_1(k3_orders_2(A_104,B_105,C_106),k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ m1_subset_1(C_106,u1_struct_0(A_104))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_orders_2(A_104)
      | ~ v5_orders_2(A_104)
      | ~ v4_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_126,plain,(
    ! [A_110,A_111,B_112,C_113] :
      ( m1_subset_1(A_110,u1_struct_0(A_111))
      | ~ r2_hidden(A_110,k3_orders_2(A_111,B_112,C_113))
      | ~ m1_subset_1(C_113,u1_struct_0(A_111))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_orders_2(A_111)
      | ~ v5_orders_2(A_111)
      | ~ v4_orders_2(A_111)
      | ~ v3_orders_2(A_111)
      | v2_struct_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_108,c_4])).

tff(c_130,plain,(
    ! [A_111,B_112,C_113] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_111,B_112,C_113)),u1_struct_0(A_111))
      | ~ m1_subset_1(C_113,u1_struct_0(A_111))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_orders_2(A_111)
      | ~ v5_orders_2(A_111)
      | ~ v4_orders_2(A_111)
      | ~ v3_orders_2(A_111)
      | v2_struct_0(A_111)
      | k3_orders_2(A_111,B_112,C_113) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_126])).

tff(c_28,plain,(
    k1_funct_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_131,plain,(
    ! [B_114,D_115,A_116,C_117] :
      ( r2_hidden(B_114,D_115)
      | ~ r2_hidden(B_114,k3_orders_2(A_116,D_115,C_117))
      | ~ m1_subset_1(D_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ m1_subset_1(C_117,u1_struct_0(A_116))
      | ~ m1_subset_1(B_114,u1_struct_0(A_116))
      | ~ l1_orders_2(A_116)
      | ~ v5_orders_2(A_116)
      | ~ v4_orders_2(A_116)
      | ~ v3_orders_2(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_210,plain,(
    ! [A_140,D_141,C_142] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_140,D_141,C_142)),D_141)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_subset_1(C_142,u1_struct_0(A_140))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_140,D_141,C_142)),u1_struct_0(A_140))
      | ~ l1_orders_2(A_140)
      | ~ v5_orders_2(A_140)
      | ~ v4_orders_2(A_140)
      | ~ v3_orders_2(A_140)
      | v2_struct_0(A_140)
      | k3_orders_2(A_140,D_141,C_142) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_131])).

tff(c_223,plain,(
    ! [A_149,B_150,C_151] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_149,B_150,C_151)),B_150)
      | ~ m1_subset_1(C_151,u1_struct_0(A_149))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_orders_2(A_149)
      | ~ v5_orders_2(A_149)
      | ~ v4_orders_2(A_149)
      | ~ v3_orders_2(A_149)
      | v2_struct_0(A_149)
      | k3_orders_2(A_149,B_150,C_151) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_130,c_210])).

tff(c_82,plain,(
    ! [A_3] :
      ( m1_subset_1(A_3,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_3,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_79,c_4])).

tff(c_215,plain,(
    ! [D_141,C_142] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_141,C_142)),D_141)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_142,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_141,C_142) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_141,C_142)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_210])).

tff(c_219,plain,(
    ! [D_141,C_142] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_141,C_142)),D_141)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_142,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_141,C_142) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_141,C_142)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_215])).

tff(c_220,plain,(
    ! [D_141,C_142] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_141,C_142)),D_141)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_142,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_141,C_142) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_141,C_142)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_219])).

tff(c_226,plain,(
    ! [C_151] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_151)),'#skF_5')
      | ~ m1_subset_1(C_151,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_151) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_223,c_220])).

tff(c_240,plain,(
    ! [C_151] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_151)),'#skF_5')
      | ~ m1_subset_1(C_151,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_151) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_79,c_226])).

tff(c_246,plain,(
    ! [C_152] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_152)),'#skF_5')
      | ~ m1_subset_1(C_152,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_152) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_240])).

tff(c_24,plain,(
    ! [A_38,D_66,B_54,E_68] :
      ( r3_orders_2(A_38,k1_funct_1(D_66,u1_struct_0(A_38)),B_54)
      | ~ r2_hidden(B_54,E_68)
      | ~ m2_orders_2(E_68,A_38,D_66)
      | ~ m1_orders_1(D_66,k1_orders_1(u1_struct_0(A_38)))
      | ~ m1_subset_1(k1_funct_1(D_66,u1_struct_0(A_38)),u1_struct_0(A_38))
      | ~ m1_subset_1(B_54,u1_struct_0(A_38))
      | ~ l1_orders_2(A_38)
      | ~ v5_orders_2(A_38)
      | ~ v4_orders_2(A_38)
      | ~ v3_orders_2(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_475,plain,(
    ! [A_198,D_199,C_200] :
      ( r3_orders_2(A_198,k1_funct_1(D_199,u1_struct_0(A_198)),'#skF_1'(k3_orders_2('#skF_2','#skF_5',C_200)))
      | ~ m2_orders_2('#skF_5',A_198,D_199)
      | ~ m1_orders_1(D_199,k1_orders_1(u1_struct_0(A_198)))
      | ~ m1_subset_1(k1_funct_1(D_199,u1_struct_0(A_198)),u1_struct_0(A_198))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_200)),u1_struct_0(A_198))
      | ~ l1_orders_2(A_198)
      | ~ v5_orders_2(A_198)
      | ~ v4_orders_2(A_198)
      | ~ v3_orders_2(A_198)
      | v2_struct_0(A_198)
      | ~ m1_subset_1(C_200,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_200) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_246,c_24])).

tff(c_480,plain,(
    ! [C_200] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_200)))
      | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_200)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_200,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_200) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_475])).

tff(c_483,plain,(
    ! [C_200] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_200)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_200)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_200,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_200) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_28,c_32,c_30,c_480])).

tff(c_485,plain,(
    ! [C_201] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_201)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_201)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_201,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_201) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_483])).

tff(c_489,plain,(
    ! [C_113] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_113)))
      | ~ m1_subset_1(C_113,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_113) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_130,c_485])).

tff(c_495,plain,(
    ! [C_113] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_113)))
      | ~ m1_subset_1(C_113,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_113) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_79,c_489])).

tff(c_498,plain,(
    ! [C_202] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_202)))
      | ~ m1_subset_1(C_202,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_202) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_495])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_orders_2(A_13,B_14,C_15)
      | ~ r3_orders_2(A_13,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_13))
      | ~ m1_subset_1(B_14,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13)
      | ~ v3_orders_2(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_500,plain,(
    ! [C_202] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_202)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_202)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_202,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_202) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_498,c_14])).

tff(c_503,plain,(
    ! [C_202] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_202)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_202)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_202,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_202) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_34,c_500])).

tff(c_505,plain,(
    ! [C_203] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_203)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_203)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_203,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_203) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_503])).

tff(c_509,plain,(
    ! [C_113] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_113)))
      | ~ m1_subset_1(C_113,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_113) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_130,c_505])).

tff(c_515,plain,(
    ! [C_113] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_113)))
      | ~ m1_subset_1(C_113,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_113) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_79,c_509])).

tff(c_518,plain,(
    ! [C_204] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_204)))
      | ~ m1_subset_1(C_204,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_204) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_515])).

tff(c_162,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( r2_orders_2(A_123,B_124,C_125)
      | ~ r2_hidden(B_124,k3_orders_2(A_123,D_126,C_125))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(C_125,u1_struct_0(A_123))
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_orders_2(A_123)
      | ~ v5_orders_2(A_123)
      | ~ v4_orders_2(A_123)
      | ~ v3_orders_2(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_255,plain,(
    ! [A_153,D_154,C_155] :
      ( r2_orders_2(A_153,'#skF_1'(k3_orders_2(A_153,D_154,C_155)),C_155)
      | ~ m1_subset_1(D_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ m1_subset_1(C_155,u1_struct_0(A_153))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_153,D_154,C_155)),u1_struct_0(A_153))
      | ~ l1_orders_2(A_153)
      | ~ v5_orders_2(A_153)
      | ~ v4_orders_2(A_153)
      | ~ v3_orders_2(A_153)
      | v2_struct_0(A_153)
      | k3_orders_2(A_153,D_154,C_155) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_162])).

tff(c_272,plain,(
    ! [A_158,B_159,C_160] :
      ( r2_orders_2(A_158,'#skF_1'(k3_orders_2(A_158,B_159,C_160)),C_160)
      | ~ m1_subset_1(C_160,u1_struct_0(A_158))
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_orders_2(A_158)
      | ~ v5_orders_2(A_158)
      | ~ v4_orders_2(A_158)
      | ~ v3_orders_2(A_158)
      | v2_struct_0(A_158)
      | k3_orders_2(A_158,B_159,C_160) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_130,c_255])).

tff(c_16,plain,(
    ! [A_16,C_22,B_20] :
      ( ~ r2_orders_2(A_16,C_22,B_20)
      | ~ r1_orders_2(A_16,B_20,C_22)
      | ~ m1_subset_1(C_22,u1_struct_0(A_16))
      | ~ m1_subset_1(B_20,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16)
      | ~ v5_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_275,plain,(
    ! [A_158,C_160,B_159] :
      ( ~ r1_orders_2(A_158,C_160,'#skF_1'(k3_orders_2(A_158,B_159,C_160)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_158,B_159,C_160)),u1_struct_0(A_158))
      | ~ m1_subset_1(C_160,u1_struct_0(A_158))
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_orders_2(A_158)
      | ~ v5_orders_2(A_158)
      | ~ v4_orders_2(A_158)
      | ~ v3_orders_2(A_158)
      | v2_struct_0(A_158)
      | k3_orders_2(A_158,B_159,C_160) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_272,c_16])).

tff(c_521,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_518,c_275])).

tff(c_527,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42,c_40,c_38,c_36,c_79,c_521])).

tff(c_528,plain,(
    ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_44,c_527])).

tff(c_535,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_130,c_528])).

tff(c_541,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_79,c_34,c_535])).

tff(c_543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_44,c_541])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.45  
% 2.87/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.46  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.87/1.46  
% 2.87/1.46  %Foreground sorts:
% 2.87/1.46  
% 2.87/1.46  
% 2.87/1.46  %Background operators:
% 2.87/1.46  
% 2.87/1.46  
% 2.87/1.46  %Foreground operators:
% 2.87/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.87/1.46  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.87/1.46  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.87/1.46  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.87/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.46  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.87/1.46  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.87/1.46  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.87/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.46  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.87/1.46  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.87/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.87/1.46  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.87/1.46  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.46  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.87/1.46  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.87/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.87/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.46  
% 3.24/1.48  tff(f_186, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_orders_1(C, k1_orders_1(u1_struct_0(A))) => (![D]: (m2_orders_2(D, A, C) => ((B = k1_funct_1(C, u1_struct_0(A))) => (k3_orders_2(A, D, B) = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_orders_2)).
% 3.24/1.48  tff(f_76, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.24/1.48  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.24/1.48  tff(f_56, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 3.24/1.48  tff(f_39, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.24/1.48  tff(f_132, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 3.24/1.48  tff(f_161, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_orders_1(D, k1_orders_1(u1_struct_0(A))) => (![E]: (m2_orders_2(E, A, D) => ((r2_hidden(B, E) & (C = k1_funct_1(D, u1_struct_0(A)))) => r3_orders_2(A, C, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_orders_2)).
% 3.24/1.48  tff(f_91, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.24/1.48  tff(f_106, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_orders_2)).
% 3.24/1.48  tff(c_26, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_186])).
% 3.24/1.48  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 3.24/1.48  tff(c_42, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 3.24/1.48  tff(c_40, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 3.24/1.48  tff(c_38, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 3.24/1.48  tff(c_36, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 3.24/1.48  tff(c_32, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 3.24/1.48  tff(c_30, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 3.24/1.48  tff(c_73, plain, (![C_97, A_98, B_99]: (m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(A_98))) | ~m2_orders_2(C_97, A_98, B_99) | ~m1_orders_1(B_99, k1_orders_1(u1_struct_0(A_98))) | ~l1_orders_2(A_98) | ~v5_orders_2(A_98) | ~v4_orders_2(A_98) | ~v3_orders_2(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.24/1.48  tff(c_75, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_73])).
% 3.24/1.48  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_32, c_75])).
% 3.24/1.48  tff(c_79, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_78])).
% 3.24/1.48  tff(c_34, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 3.24/1.48  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.24/1.48  tff(c_108, plain, (![A_104, B_105, C_106]: (m1_subset_1(k3_orders_2(A_104, B_105, C_106), k1_zfmisc_1(u1_struct_0(A_104))) | ~m1_subset_1(C_106, u1_struct_0(A_104)) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_orders_2(A_104) | ~v5_orders_2(A_104) | ~v4_orders_2(A_104) | ~v3_orders_2(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.24/1.48  tff(c_4, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.24/1.48  tff(c_126, plain, (![A_110, A_111, B_112, C_113]: (m1_subset_1(A_110, u1_struct_0(A_111)) | ~r2_hidden(A_110, k3_orders_2(A_111, B_112, C_113)) | ~m1_subset_1(C_113, u1_struct_0(A_111)) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_orders_2(A_111) | ~v5_orders_2(A_111) | ~v4_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111))), inference(resolution, [status(thm)], [c_108, c_4])).
% 3.24/1.48  tff(c_130, plain, (![A_111, B_112, C_113]: (m1_subset_1('#skF_1'(k3_orders_2(A_111, B_112, C_113)), u1_struct_0(A_111)) | ~m1_subset_1(C_113, u1_struct_0(A_111)) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_orders_2(A_111) | ~v5_orders_2(A_111) | ~v4_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111) | k3_orders_2(A_111, B_112, C_113)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_126])).
% 3.24/1.48  tff(c_28, plain, (k1_funct_1('#skF_4', u1_struct_0('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_186])).
% 3.24/1.48  tff(c_131, plain, (![B_114, D_115, A_116, C_117]: (r2_hidden(B_114, D_115) | ~r2_hidden(B_114, k3_orders_2(A_116, D_115, C_117)) | ~m1_subset_1(D_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~m1_subset_1(C_117, u1_struct_0(A_116)) | ~m1_subset_1(B_114, u1_struct_0(A_116)) | ~l1_orders_2(A_116) | ~v5_orders_2(A_116) | ~v4_orders_2(A_116) | ~v3_orders_2(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.24/1.48  tff(c_210, plain, (![A_140, D_141, C_142]: (r2_hidden('#skF_1'(k3_orders_2(A_140, D_141, C_142)), D_141) | ~m1_subset_1(D_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~m1_subset_1(C_142, u1_struct_0(A_140)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_140, D_141, C_142)), u1_struct_0(A_140)) | ~l1_orders_2(A_140) | ~v5_orders_2(A_140) | ~v4_orders_2(A_140) | ~v3_orders_2(A_140) | v2_struct_0(A_140) | k3_orders_2(A_140, D_141, C_142)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_131])).
% 3.24/1.48  tff(c_223, plain, (![A_149, B_150, C_151]: (r2_hidden('#skF_1'(k3_orders_2(A_149, B_150, C_151)), B_150) | ~m1_subset_1(C_151, u1_struct_0(A_149)) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_orders_2(A_149) | ~v5_orders_2(A_149) | ~v4_orders_2(A_149) | ~v3_orders_2(A_149) | v2_struct_0(A_149) | k3_orders_2(A_149, B_150, C_151)=k1_xboole_0)), inference(resolution, [status(thm)], [c_130, c_210])).
% 3.24/1.48  tff(c_82, plain, (![A_3]: (m1_subset_1(A_3, u1_struct_0('#skF_2')) | ~r2_hidden(A_3, '#skF_5'))), inference(resolution, [status(thm)], [c_79, c_4])).
% 3.24/1.48  tff(c_215, plain, (![D_141, C_142]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_141, C_142)), D_141) | ~m1_subset_1(D_141, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_142, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_141, C_142)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_141, C_142)), '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_210])).
% 3.24/1.48  tff(c_219, plain, (![D_141, C_142]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_141, C_142)), D_141) | ~m1_subset_1(D_141, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_142, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_141, C_142)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_141, C_142)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_215])).
% 3.24/1.48  tff(c_220, plain, (![D_141, C_142]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_141, C_142)), D_141) | ~m1_subset_1(D_141, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_142, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_141, C_142)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_141, C_142)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_44, c_219])).
% 3.24/1.48  tff(c_226, plain, (![C_151]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_151)), '#skF_5') | ~m1_subset_1(C_151, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_151)=k1_xboole_0)), inference(resolution, [status(thm)], [c_223, c_220])).
% 3.24/1.48  tff(c_240, plain, (![C_151]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_151)), '#skF_5') | ~m1_subset_1(C_151, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_151)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_79, c_226])).
% 3.24/1.48  tff(c_246, plain, (![C_152]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_152)), '#skF_5') | ~m1_subset_1(C_152, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_152)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44, c_240])).
% 3.24/1.48  tff(c_24, plain, (![A_38, D_66, B_54, E_68]: (r3_orders_2(A_38, k1_funct_1(D_66, u1_struct_0(A_38)), B_54) | ~r2_hidden(B_54, E_68) | ~m2_orders_2(E_68, A_38, D_66) | ~m1_orders_1(D_66, k1_orders_1(u1_struct_0(A_38))) | ~m1_subset_1(k1_funct_1(D_66, u1_struct_0(A_38)), u1_struct_0(A_38)) | ~m1_subset_1(B_54, u1_struct_0(A_38)) | ~l1_orders_2(A_38) | ~v5_orders_2(A_38) | ~v4_orders_2(A_38) | ~v3_orders_2(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.24/1.48  tff(c_475, plain, (![A_198, D_199, C_200]: (r3_orders_2(A_198, k1_funct_1(D_199, u1_struct_0(A_198)), '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_200))) | ~m2_orders_2('#skF_5', A_198, D_199) | ~m1_orders_1(D_199, k1_orders_1(u1_struct_0(A_198))) | ~m1_subset_1(k1_funct_1(D_199, u1_struct_0(A_198)), u1_struct_0(A_198)) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_200)), u1_struct_0(A_198)) | ~l1_orders_2(A_198) | ~v5_orders_2(A_198) | ~v4_orders_2(A_198) | ~v3_orders_2(A_198) | v2_struct_0(A_198) | ~m1_subset_1(C_200, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_200)=k1_xboole_0)), inference(resolution, [status(thm)], [c_246, c_24])).
% 3.24/1.48  tff(c_480, plain, (![C_200]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_200))) | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_200)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_200, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_200)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_475])).
% 3.24/1.48  tff(c_483, plain, (![C_200]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_200))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_200)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_200, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_200)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_28, c_32, c_30, c_480])).
% 3.24/1.48  tff(c_485, plain, (![C_201]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_201))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_201)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_201, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_201)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44, c_483])).
% 3.24/1.48  tff(c_489, plain, (![C_113]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_113))) | ~m1_subset_1(C_113, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_113)=k1_xboole_0)), inference(resolution, [status(thm)], [c_130, c_485])).
% 3.24/1.48  tff(c_495, plain, (![C_113]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_113))) | ~m1_subset_1(C_113, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_113)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_79, c_489])).
% 3.24/1.48  tff(c_498, plain, (![C_202]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_202))) | ~m1_subset_1(C_202, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_202)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44, c_495])).
% 3.24/1.48  tff(c_14, plain, (![A_13, B_14, C_15]: (r1_orders_2(A_13, B_14, C_15) | ~r3_orders_2(A_13, B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_13)) | ~m1_subset_1(B_14, u1_struct_0(A_13)) | ~l1_orders_2(A_13) | ~v3_orders_2(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.24/1.48  tff(c_500, plain, (![C_202]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_202))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_202)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_202, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_202)=k1_xboole_0)), inference(resolution, [status(thm)], [c_498, c_14])).
% 3.24/1.48  tff(c_503, plain, (![C_202]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_202))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_202)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_202, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_202)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_34, c_500])).
% 3.24/1.48  tff(c_505, plain, (![C_203]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_203))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_203)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_203, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_203)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44, c_503])).
% 3.24/1.48  tff(c_509, plain, (![C_113]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_113))) | ~m1_subset_1(C_113, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_113)=k1_xboole_0)), inference(resolution, [status(thm)], [c_130, c_505])).
% 3.24/1.48  tff(c_515, plain, (![C_113]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_113))) | ~m1_subset_1(C_113, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_113)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_79, c_509])).
% 3.24/1.48  tff(c_518, plain, (![C_204]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_204))) | ~m1_subset_1(C_204, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_204)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44, c_515])).
% 3.24/1.48  tff(c_162, plain, (![A_123, B_124, C_125, D_126]: (r2_orders_2(A_123, B_124, C_125) | ~r2_hidden(B_124, k3_orders_2(A_123, D_126, C_125)) | ~m1_subset_1(D_126, k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_subset_1(C_125, u1_struct_0(A_123)) | ~m1_subset_1(B_124, u1_struct_0(A_123)) | ~l1_orders_2(A_123) | ~v5_orders_2(A_123) | ~v4_orders_2(A_123) | ~v3_orders_2(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.24/1.48  tff(c_255, plain, (![A_153, D_154, C_155]: (r2_orders_2(A_153, '#skF_1'(k3_orders_2(A_153, D_154, C_155)), C_155) | ~m1_subset_1(D_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~m1_subset_1(C_155, u1_struct_0(A_153)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_153, D_154, C_155)), u1_struct_0(A_153)) | ~l1_orders_2(A_153) | ~v5_orders_2(A_153) | ~v4_orders_2(A_153) | ~v3_orders_2(A_153) | v2_struct_0(A_153) | k3_orders_2(A_153, D_154, C_155)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_162])).
% 3.24/1.48  tff(c_272, plain, (![A_158, B_159, C_160]: (r2_orders_2(A_158, '#skF_1'(k3_orders_2(A_158, B_159, C_160)), C_160) | ~m1_subset_1(C_160, u1_struct_0(A_158)) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_orders_2(A_158) | ~v5_orders_2(A_158) | ~v4_orders_2(A_158) | ~v3_orders_2(A_158) | v2_struct_0(A_158) | k3_orders_2(A_158, B_159, C_160)=k1_xboole_0)), inference(resolution, [status(thm)], [c_130, c_255])).
% 3.24/1.48  tff(c_16, plain, (![A_16, C_22, B_20]: (~r2_orders_2(A_16, C_22, B_20) | ~r1_orders_2(A_16, B_20, C_22) | ~m1_subset_1(C_22, u1_struct_0(A_16)) | ~m1_subset_1(B_20, u1_struct_0(A_16)) | ~l1_orders_2(A_16) | ~v5_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.24/1.48  tff(c_275, plain, (![A_158, C_160, B_159]: (~r1_orders_2(A_158, C_160, '#skF_1'(k3_orders_2(A_158, B_159, C_160))) | ~m1_subset_1('#skF_1'(k3_orders_2(A_158, B_159, C_160)), u1_struct_0(A_158)) | ~m1_subset_1(C_160, u1_struct_0(A_158)) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_orders_2(A_158) | ~v5_orders_2(A_158) | ~v4_orders_2(A_158) | ~v3_orders_2(A_158) | v2_struct_0(A_158) | k3_orders_2(A_158, B_159, C_160)=k1_xboole_0)), inference(resolution, [status(thm)], [c_272, c_16])).
% 3.24/1.48  tff(c_521, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_518, c_275])).
% 3.24/1.48  tff(c_527, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42, c_40, c_38, c_36, c_79, c_521])).
% 3.24/1.48  tff(c_528, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_44, c_527])).
% 3.24/1.48  tff(c_535, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_130, c_528])).
% 3.24/1.48  tff(c_541, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_79, c_34, c_535])).
% 3.24/1.48  tff(c_543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_44, c_541])).
% 3.24/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.48  
% 3.24/1.48  Inference rules
% 3.24/1.48  ----------------------
% 3.24/1.48  #Ref     : 0
% 3.24/1.48  #Sup     : 86
% 3.24/1.48  #Fact    : 0
% 3.24/1.48  #Define  : 0
% 3.24/1.48  #Split   : 1
% 3.24/1.48  #Chain   : 0
% 3.24/1.48  #Close   : 0
% 3.24/1.48  
% 3.24/1.48  Ordering : KBO
% 3.24/1.48  
% 3.24/1.48  Simplification rules
% 3.24/1.48  ----------------------
% 3.24/1.48  #Subsume      : 23
% 3.24/1.48  #Demod        : 179
% 3.24/1.48  #Tautology    : 12
% 3.24/1.48  #SimpNegUnit  : 42
% 3.24/1.48  #BackRed      : 0
% 3.24/1.48  
% 3.24/1.48  #Partial instantiations: 0
% 3.24/1.48  #Strategies tried      : 1
% 3.24/1.48  
% 3.24/1.48  Timing (in seconds)
% 3.24/1.48  ----------------------
% 3.24/1.48  Preprocessing        : 0.33
% 3.24/1.48  Parsing              : 0.19
% 3.24/1.48  CNF conversion       : 0.03
% 3.24/1.48  Main loop            : 0.37
% 3.24/1.48  Inferencing          : 0.15
% 3.24/1.48  Reduction            : 0.10
% 3.24/1.48  Demodulation         : 0.07
% 3.24/1.48  BG Simplification    : 0.02
% 3.24/1.48  Subsumption          : 0.07
% 3.24/1.48  Abstraction          : 0.01
% 3.24/1.48  MUC search           : 0.00
% 3.24/1.48  Cooper               : 0.00
% 3.24/1.48  Total                : 0.74
% 3.24/1.48  Index Insertion      : 0.00
% 3.24/1.48  Index Deletion       : 0.00
% 3.24/1.48  Index Matching       : 0.00
% 3.24/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
