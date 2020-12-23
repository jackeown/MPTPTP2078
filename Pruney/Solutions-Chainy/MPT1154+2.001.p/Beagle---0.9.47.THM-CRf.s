%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:32 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 367 expanded)
%              Number of leaves         :   35 ( 141 expanded)
%              Depth                    :   14
%              Number of atoms          :  162 ( 953 expanded)
%              Number of equality atoms :   17 ( 163 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_zfmisc_1 > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_orders_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_49,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( r2_hidden(B,C)
                  & r2_hidden(B,k1_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_134,plain,(
    ! [A_45,B_46] :
      ( k6_domain_1(A_45,B_46) = k1_tarski(B_46)
      | ~ m1_subset_1(B_46,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_138,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_134])).

tff(c_139,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_143,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_139,c_6])).

tff(c_147,plain,(
    m1_subset_1('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_42])).

tff(c_26,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_296,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_69),B_70),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(B_70,u1_struct_0(A_69))
      | ~ l1_orders_2(A_69)
      | ~ v3_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_302,plain,(
    ! [B_70] :
      ( m1_subset_1(k6_domain_1(k1_xboole_0,B_70),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_70,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_296])).

tff(c_308,plain,(
    ! [B_70] :
      ( m1_subset_1(k6_domain_1(k1_xboole_0,B_70),k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(B_70,k1_xboole_0)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_143,c_26,c_143,c_302])).

tff(c_313,plain,(
    ! [B_71] :
      ( m1_subset_1(k6_domain_1(k1_xboole_0,B_71),k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(B_71,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_308])).

tff(c_144,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_139])).

tff(c_24,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_162,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_xboole_0(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_165,plain,(
    ! [C_47] :
      ( v1_xboole_0(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_162])).

tff(c_170,plain,(
    ! [C_47] :
      ( v1_xboole_0(C_47)
      | ~ m1_subset_1(C_47,k1_tarski(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_26,c_165])).

tff(c_324,plain,(
    ! [B_72] :
      ( v1_xboole_0(k6_domain_1(k1_xboole_0,B_72))
      | ~ m1_subset_1(B_72,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_313,c_170])).

tff(c_332,plain,(
    ! [B_73] :
      ( k6_domain_1(k1_xboole_0,B_73) = k1_xboole_0
      | ~ m1_subset_1(B_73,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_324,c_6])).

tff(c_336,plain,(
    k6_domain_1(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_147,c_332])).

tff(c_40,plain,(
    r2_hidden('#skF_5',k1_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_133,plain,(
    ~ v1_xboole_0(k1_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'))) ),
    inference(resolution,[status(thm)],[c_40,c_2])).

tff(c_145,plain,(
    ~ v1_xboole_0(k1_orders_2('#skF_4',k6_domain_1(k1_xboole_0,'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_133])).

tff(c_338,plain,(
    ~ v1_xboole_0(k1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_145])).

tff(c_309,plain,(
    ! [B_70] :
      ( m1_subset_1(k6_domain_1(k1_xboole_0,B_70),k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(B_70,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_308])).

tff(c_345,plain,
    ( m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ m1_subset_1('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_309])).

tff(c_354,plain,(
    m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_345])).

tff(c_373,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1(k1_orders_2(A_74,B_75),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_orders_2(A_74)
      | ~ v5_orders_2(A_74)
      | ~ v4_orders_2(A_74)
      | ~ v3_orders_2(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_379,plain,(
    ! [B_75] :
      ( m1_subset_1(k1_orders_2('#skF_4',B_75),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_373])).

tff(c_382,plain,(
    ! [B_75] :
      ( m1_subset_1(k1_orders_2('#skF_4',B_75),k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(B_75,k1_tarski(k1_xboole_0))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_26,c_143,c_26,c_379])).

tff(c_388,plain,(
    ! [B_76] :
      ( m1_subset_1(k1_orders_2('#skF_4',B_76),k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(B_76,k1_tarski(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_382])).

tff(c_399,plain,(
    ! [B_77] :
      ( v1_xboole_0(k1_orders_2('#skF_4',B_77))
      | ~ m1_subset_1(B_77,k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_388,c_170])).

tff(c_405,plain,(
    v1_xboole_0(k1_orders_2('#skF_4',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_354,c_399])).

tff(c_413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_405])).

tff(c_414,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_503,plain,(
    ! [A_99,B_100] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_99),B_100),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ l1_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_509,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_503])).

tff(c_512,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_42,c_509])).

tff(c_513,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_512])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_417,plain,(
    r2_hidden('#skF_5',k1_orders_2('#skF_4',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_40])).

tff(c_551,plain,(
    ! [B_107,A_108,C_109] :
      ( ~ r2_hidden(B_107,k1_orders_2(A_108,C_109))
      | ~ r2_hidden(B_107,C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(B_107,u1_struct_0(A_108))
      | ~ l1_orders_2(A_108)
      | ~ v5_orders_2(A_108)
      | ~ v4_orders_2(A_108)
      | ~ v3_orders_2(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_562,plain,
    ( ~ r2_hidden('#skF_5',k1_tarski('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_417,c_551])).

tff(c_568,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_513,c_10,c_562])).

tff(c_570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_568])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:09:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.45  
% 2.43/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.45  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_zfmisc_1 > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.82/1.45  
% 2.82/1.45  %Foreground sorts:
% 2.82/1.45  
% 2.82/1.45  
% 2.82/1.45  %Background operators:
% 2.82/1.45  
% 2.82/1.45  
% 2.82/1.45  %Foreground operators:
% 2.82/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.82/1.45  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.82/1.45  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.82/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.82/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.82/1.45  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.82/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.45  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.82/1.45  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.82/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.82/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.82/1.45  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.82/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.82/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.45  
% 2.82/1.47  tff(f_132, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_orders_2)).
% 2.82/1.47  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.82/1.47  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 2.82/1.47  tff(f_49, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.82/1.47  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 2.82/1.47  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.82/1.47  tff(f_56, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 2.82/1.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.82/1.47  tff(f_71, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 2.82/1.47  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.82/1.47  tff(f_114, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_orders_2)).
% 2.82/1.47  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.82/1.47  tff(c_50, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.82/1.47  tff(c_48, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.82/1.47  tff(c_46, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.82/1.47  tff(c_44, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.82/1.47  tff(c_42, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.82/1.47  tff(c_134, plain, (![A_45, B_46]: (k6_domain_1(A_45, B_46)=k1_tarski(B_46) | ~m1_subset_1(B_46, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.82/1.47  tff(c_138, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_134])).
% 2.82/1.47  tff(c_139, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_138])).
% 2.82/1.47  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.82/1.47  tff(c_143, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_139, c_6])).
% 2.82/1.47  tff(c_147, plain, (m1_subset_1('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_143, c_42])).
% 2.82/1.47  tff(c_26, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.82/1.47  tff(c_296, plain, (![A_69, B_70]: (m1_subset_1(k6_domain_1(u1_struct_0(A_69), B_70), k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(B_70, u1_struct_0(A_69)) | ~l1_orders_2(A_69) | ~v3_orders_2(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.82/1.47  tff(c_302, plain, (![B_70]: (m1_subset_1(k6_domain_1(k1_xboole_0, B_70), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_70, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_296])).
% 2.82/1.47  tff(c_308, plain, (![B_70]: (m1_subset_1(k6_domain_1(k1_xboole_0, B_70), k1_tarski(k1_xboole_0)) | ~m1_subset_1(B_70, k1_xboole_0) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_143, c_26, c_143, c_302])).
% 2.82/1.47  tff(c_313, plain, (![B_71]: (m1_subset_1(k6_domain_1(k1_xboole_0, B_71), k1_tarski(k1_xboole_0)) | ~m1_subset_1(B_71, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_52, c_308])).
% 2.82/1.47  tff(c_144, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_143, c_139])).
% 2.82/1.47  tff(c_24, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.82/1.47  tff(c_162, plain, (![C_47, A_48, B_49]: (v1_xboole_0(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.82/1.47  tff(c_165, plain, (![C_47]: (v1_xboole_0(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_162])).
% 2.82/1.47  tff(c_170, plain, (![C_47]: (v1_xboole_0(C_47) | ~m1_subset_1(C_47, k1_tarski(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_26, c_165])).
% 2.82/1.47  tff(c_324, plain, (![B_72]: (v1_xboole_0(k6_domain_1(k1_xboole_0, B_72)) | ~m1_subset_1(B_72, k1_xboole_0))), inference(resolution, [status(thm)], [c_313, c_170])).
% 2.82/1.47  tff(c_332, plain, (![B_73]: (k6_domain_1(k1_xboole_0, B_73)=k1_xboole_0 | ~m1_subset_1(B_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_324, c_6])).
% 2.82/1.47  tff(c_336, plain, (k6_domain_1(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_147, c_332])).
% 2.82/1.47  tff(c_40, plain, (r2_hidden('#skF_5', k1_orders_2('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.82/1.47  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.47  tff(c_133, plain, (~v1_xboole_0(k1_orders_2('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')))), inference(resolution, [status(thm)], [c_40, c_2])).
% 2.82/1.47  tff(c_145, plain, (~v1_xboole_0(k1_orders_2('#skF_4', k6_domain_1(k1_xboole_0, '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_133])).
% 2.82/1.47  tff(c_338, plain, (~v1_xboole_0(k1_orders_2('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_145])).
% 2.82/1.47  tff(c_309, plain, (![B_70]: (m1_subset_1(k6_domain_1(k1_xboole_0, B_70), k1_tarski(k1_xboole_0)) | ~m1_subset_1(B_70, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_52, c_308])).
% 2.82/1.47  tff(c_345, plain, (m1_subset_1(k1_xboole_0, k1_tarski(k1_xboole_0)) | ~m1_subset_1('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_336, c_309])).
% 2.82/1.47  tff(c_354, plain, (m1_subset_1(k1_xboole_0, k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_345])).
% 2.82/1.47  tff(c_373, plain, (![A_74, B_75]: (m1_subset_1(k1_orders_2(A_74, B_75), k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_orders_2(A_74) | ~v5_orders_2(A_74) | ~v4_orders_2(A_74) | ~v3_orders_2(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.82/1.47  tff(c_379, plain, (![B_75]: (m1_subset_1(k1_orders_2('#skF_4', B_75), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_373])).
% 2.82/1.47  tff(c_382, plain, (![B_75]: (m1_subset_1(k1_orders_2('#skF_4', B_75), k1_tarski(k1_xboole_0)) | ~m1_subset_1(B_75, k1_tarski(k1_xboole_0)) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_26, c_143, c_26, c_379])).
% 2.82/1.47  tff(c_388, plain, (![B_76]: (m1_subset_1(k1_orders_2('#skF_4', B_76), k1_tarski(k1_xboole_0)) | ~m1_subset_1(B_76, k1_tarski(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_52, c_382])).
% 2.82/1.47  tff(c_399, plain, (![B_77]: (v1_xboole_0(k1_orders_2('#skF_4', B_77)) | ~m1_subset_1(B_77, k1_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_388, c_170])).
% 2.82/1.47  tff(c_405, plain, (v1_xboole_0(k1_orders_2('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_354, c_399])).
% 2.82/1.47  tff(c_413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_338, c_405])).
% 2.82/1.47  tff(c_414, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_138])).
% 2.82/1.47  tff(c_503, plain, (![A_99, B_100]: (m1_subset_1(k6_domain_1(u1_struct_0(A_99), B_100), k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_subset_1(B_100, u1_struct_0(A_99)) | ~l1_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.82/1.47  tff(c_509, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_414, c_503])).
% 2.82/1.47  tff(c_512, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_42, c_509])).
% 2.82/1.47  tff(c_513, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_512])).
% 2.82/1.47  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.82/1.47  tff(c_417, plain, (r2_hidden('#skF_5', k1_orders_2('#skF_4', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_414, c_40])).
% 2.82/1.47  tff(c_551, plain, (![B_107, A_108, C_109]: (~r2_hidden(B_107, k1_orders_2(A_108, C_109)) | ~r2_hidden(B_107, C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(B_107, u1_struct_0(A_108)) | ~l1_orders_2(A_108) | ~v5_orders_2(A_108) | ~v4_orders_2(A_108) | ~v3_orders_2(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.82/1.47  tff(c_562, plain, (~r2_hidden('#skF_5', k1_tarski('#skF_5')) | ~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_417, c_551])).
% 2.82/1.47  tff(c_568, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_513, c_10, c_562])).
% 2.82/1.47  tff(c_570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_568])).
% 2.82/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.47  
% 2.82/1.47  Inference rules
% 2.82/1.47  ----------------------
% 2.82/1.47  #Ref     : 0
% 2.82/1.47  #Sup     : 107
% 2.82/1.47  #Fact    : 0
% 2.82/1.47  #Define  : 0
% 2.82/1.47  #Split   : 3
% 2.82/1.47  #Chain   : 0
% 2.82/1.47  #Close   : 0
% 2.82/1.47  
% 2.82/1.47  Ordering : KBO
% 2.82/1.47  
% 2.82/1.47  Simplification rules
% 2.82/1.47  ----------------------
% 2.82/1.47  #Subsume      : 13
% 2.82/1.47  #Demod        : 74
% 2.82/1.47  #Tautology    : 58
% 2.82/1.47  #SimpNegUnit  : 17
% 2.82/1.47  #BackRed      : 10
% 2.82/1.47  
% 2.82/1.47  #Partial instantiations: 0
% 2.82/1.47  #Strategies tried      : 1
% 2.82/1.47  
% 2.82/1.47  Timing (in seconds)
% 2.82/1.47  ----------------------
% 2.82/1.47  Preprocessing        : 0.33
% 2.82/1.47  Parsing              : 0.17
% 2.82/1.47  CNF conversion       : 0.02
% 2.82/1.47  Main loop            : 0.30
% 2.82/1.47  Inferencing          : 0.11
% 2.82/1.47  Reduction            : 0.09
% 2.82/1.47  Demodulation         : 0.06
% 2.82/1.47  BG Simplification    : 0.02
% 2.82/1.47  Subsumption          : 0.05
% 2.82/1.47  Abstraction          : 0.02
% 2.82/1.47  MUC search           : 0.00
% 2.82/1.47  Cooper               : 0.00
% 2.82/1.47  Total                : 0.66
% 2.82/1.47  Index Insertion      : 0.00
% 2.82/1.47  Index Deletion       : 0.00
% 2.82/1.47  Index Matching       : 0.00
% 2.82/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
