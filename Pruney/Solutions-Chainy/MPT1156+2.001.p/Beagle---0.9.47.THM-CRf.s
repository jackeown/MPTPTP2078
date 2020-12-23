%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:37 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 351 expanded)
%              Number of leaves         :   34 ( 133 expanded)
%              Depth                    :   14
%              Number of atoms          :  160 ( 937 expanded)
%              Number of equality atoms :   15 ( 147 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_zfmisc_1 > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

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

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

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

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k2_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_orders_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(A),B),A)
            & m1_subset_1(k6_domain_1(u1_struct_0(A),B),k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_113,axiom,(
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
                  & r2_hidden(B,k2_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_orders_2)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_48,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_46,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_42,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_128,plain,(
    ! [A_45,B_46] :
      ( k6_domain_1(A_45,B_46) = k1_tarski(B_46)
      | ~ m1_subset_1(B_46,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_132,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_128])).

tff(c_133,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_137,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_133,c_6])).

tff(c_141,plain,(
    m1_subset_1('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_40])).

tff(c_286,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_71),B_72),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l1_orders_2(A_71)
      | ~ v3_orders_2(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_292,plain,(
    ! [B_72] :
      ( m1_subset_1(k6_domain_1(k1_xboole_0,B_72),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_72,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_286])).

tff(c_298,plain,(
    ! [B_72] :
      ( m1_subset_1(k6_domain_1(k1_xboole_0,B_72),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(B_72,k1_xboole_0)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_137,c_137,c_292])).

tff(c_314,plain,(
    ! [B_75] :
      ( m1_subset_1(k6_domain_1(k1_xboole_0,B_75),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(B_75,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_298])).

tff(c_138,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_133])).

tff(c_24,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_156,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_xboole_0(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_159,plain,(
    ! [C_47] :
      ( v1_xboole_0(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_156])).

tff(c_164,plain,(
    ! [C_47] :
      ( v1_xboole_0(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_159])).

tff(c_323,plain,(
    ! [B_76] :
      ( v1_xboole_0(k6_domain_1(k1_xboole_0,B_76))
      | ~ m1_subset_1(B_76,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_314,c_164])).

tff(c_331,plain,(
    ! [B_77] :
      ( k6_domain_1(k1_xboole_0,B_77) = k1_xboole_0
      | ~ m1_subset_1(B_77,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_323,c_6])).

tff(c_335,plain,(
    k6_domain_1(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_141,c_331])).

tff(c_38,plain,(
    r2_hidden('#skF_5',k2_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_75,plain,(
    ! [B_36,A_37] :
      ( ~ r2_hidden(B_36,A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ~ v1_xboole_0(k2_orders_2('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_5'))) ),
    inference(resolution,[status(thm)],[c_38,c_75])).

tff(c_139,plain,(
    ~ v1_xboole_0(k2_orders_2('#skF_4',k6_domain_1(k1_xboole_0,'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_82])).

tff(c_337,plain,(
    ~ v1_xboole_0(k2_orders_2('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_139])).

tff(c_299,plain,(
    ! [B_72] :
      ( m1_subset_1(k6_domain_1(k1_xboole_0,B_72),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(B_72,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_298])).

tff(c_344,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_299])).

tff(c_353,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_344])).

tff(c_303,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k2_orders_2(A_73,B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_309,plain,(
    ! [B_74] :
      ( m1_subset_1(k2_orders_2('#skF_4',B_74),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_303])).

tff(c_312,plain,(
    ! [B_74] :
      ( m1_subset_1(k2_orders_2('#skF_4',B_74),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_xboole_0))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_137,c_309])).

tff(c_733,plain,(
    ! [B_101] :
      ( m1_subset_1(k2_orders_2('#skF_4',B_101),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_312])).

tff(c_744,plain,(
    ! [B_102] :
      ( v1_xboole_0(k2_orders_2('#skF_4',B_102))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_733,c_164])).

tff(c_750,plain,(
    v1_xboole_0(k2_orders_2('#skF_4',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_353,c_744])).

tff(c_758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_750])).

tff(c_759,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_845,plain,(
    ! [A_122,B_123] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(A_122),B_123),k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | ~ v3_orders_2(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_851,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_845])).

tff(c_854,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_40,c_851])).

tff(c_855,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_854])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_762,plain,(
    r2_hidden('#skF_5',k2_orders_2('#skF_4',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_38])).

tff(c_894,plain,(
    ! [B_132,A_133,C_134] :
      ( ~ r2_hidden(B_132,k2_orders_2(A_133,C_134))
      | ~ r2_hidden(B_132,C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ m1_subset_1(B_132,u1_struct_0(A_133))
      | ~ l1_orders_2(A_133)
      | ~ v5_orders_2(A_133)
      | ~ v4_orders_2(A_133)
      | ~ v3_orders_2(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_905,plain,
    ( ~ r2_hidden('#skF_5',k1_tarski('#skF_5'))
    | ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_762,c_894])).

tff(c_911,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_855,c_10,c_905])).

tff(c_913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_911])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:22:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.46  
% 3.17/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.46  %$ v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k6_domain_1 > k2_zfmisc_1 > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 3.17/1.46  
% 3.17/1.46  %Foreground sorts:
% 3.17/1.46  
% 3.17/1.46  
% 3.17/1.46  %Background operators:
% 3.17/1.46  
% 3.17/1.46  
% 3.17/1.46  %Foreground operators:
% 3.17/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.17/1.46  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.17/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.17/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.17/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.17/1.46  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.17/1.46  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 3.17/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.17/1.46  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.17/1.46  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.17/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.46  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.17/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.17/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.17/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.17/1.46  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.17/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.17/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.17/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.46  
% 3.17/1.48  tff(f_131, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_orders_2)).
% 3.17/1.48  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.17/1.48  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 3.17/1.48  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v6_orders_2(k6_domain_1(u1_struct_0(A), B), A) & m1_subset_1(k6_domain_1(u1_struct_0(A), B), k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 3.17/1.48  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.17/1.48  tff(f_55, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 3.17/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.17/1.48  tff(f_70, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 3.17/1.48  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.17/1.48  tff(f_113, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_orders_2)).
% 3.17/1.48  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.17/1.48  tff(c_48, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.17/1.48  tff(c_46, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.17/1.48  tff(c_44, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.17/1.48  tff(c_42, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.17/1.48  tff(c_40, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.17/1.48  tff(c_128, plain, (![A_45, B_46]: (k6_domain_1(A_45, B_46)=k1_tarski(B_46) | ~m1_subset_1(B_46, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.17/1.48  tff(c_132, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_128])).
% 3.17/1.48  tff(c_133, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_132])).
% 3.17/1.48  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.17/1.48  tff(c_137, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_133, c_6])).
% 3.17/1.48  tff(c_141, plain, (m1_subset_1('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_137, c_40])).
% 3.17/1.48  tff(c_286, plain, (![A_71, B_72]: (m1_subset_1(k6_domain_1(u1_struct_0(A_71), B_72), k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l1_orders_2(A_71) | ~v3_orders_2(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.17/1.48  tff(c_292, plain, (![B_72]: (m1_subset_1(k6_domain_1(k1_xboole_0, B_72), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_72, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_286])).
% 3.17/1.48  tff(c_298, plain, (![B_72]: (m1_subset_1(k6_domain_1(k1_xboole_0, B_72), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(B_72, k1_xboole_0) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_137, c_137, c_292])).
% 3.17/1.48  tff(c_314, plain, (![B_75]: (m1_subset_1(k6_domain_1(k1_xboole_0, B_75), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(B_75, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_50, c_298])).
% 3.17/1.48  tff(c_138, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_137, c_133])).
% 3.17/1.48  tff(c_24, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.17/1.48  tff(c_156, plain, (![C_47, A_48, B_49]: (v1_xboole_0(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.17/1.48  tff(c_159, plain, (![C_47]: (v1_xboole_0(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_156])).
% 3.17/1.48  tff(c_164, plain, (![C_47]: (v1_xboole_0(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_159])).
% 3.17/1.48  tff(c_323, plain, (![B_76]: (v1_xboole_0(k6_domain_1(k1_xboole_0, B_76)) | ~m1_subset_1(B_76, k1_xboole_0))), inference(resolution, [status(thm)], [c_314, c_164])).
% 3.17/1.48  tff(c_331, plain, (![B_77]: (k6_domain_1(k1_xboole_0, B_77)=k1_xboole_0 | ~m1_subset_1(B_77, k1_xboole_0))), inference(resolution, [status(thm)], [c_323, c_6])).
% 3.17/1.48  tff(c_335, plain, (k6_domain_1(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_141, c_331])).
% 3.17/1.48  tff(c_38, plain, (r2_hidden('#skF_5', k2_orders_2('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.17/1.48  tff(c_75, plain, (![B_36, A_37]: (~r2_hidden(B_36, A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.17/1.48  tff(c_82, plain, (~v1_xboole_0(k2_orders_2('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')))), inference(resolution, [status(thm)], [c_38, c_75])).
% 3.17/1.48  tff(c_139, plain, (~v1_xboole_0(k2_orders_2('#skF_4', k6_domain_1(k1_xboole_0, '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_82])).
% 3.17/1.48  tff(c_337, plain, (~v1_xboole_0(k2_orders_2('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_139])).
% 3.17/1.48  tff(c_299, plain, (![B_72]: (m1_subset_1(k6_domain_1(k1_xboole_0, B_72), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(B_72, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_50, c_298])).
% 3.17/1.48  tff(c_344, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_335, c_299])).
% 3.17/1.48  tff(c_353, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_344])).
% 3.17/1.48  tff(c_303, plain, (![A_73, B_74]: (m1_subset_1(k2_orders_2(A_73, B_74), k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.17/1.48  tff(c_309, plain, (![B_74]: (m1_subset_1(k2_orders_2('#skF_4', B_74), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_303])).
% 3.17/1.48  tff(c_312, plain, (![B_74]: (m1_subset_1(k2_orders_2('#skF_4', B_74), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_137, c_309])).
% 3.17/1.48  tff(c_733, plain, (![B_101]: (m1_subset_1(k2_orders_2('#skF_4', B_101), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(B_101, k1_zfmisc_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_50, c_312])).
% 3.17/1.48  tff(c_744, plain, (![B_102]: (v1_xboole_0(k2_orders_2('#skF_4', B_102)) | ~m1_subset_1(B_102, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_733, c_164])).
% 3.17/1.48  tff(c_750, plain, (v1_xboole_0(k2_orders_2('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_353, c_744])).
% 3.17/1.48  tff(c_758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_337, c_750])).
% 3.17/1.48  tff(c_759, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_5')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_132])).
% 3.17/1.48  tff(c_845, plain, (![A_122, B_123]: (m1_subset_1(k6_domain_1(u1_struct_0(A_122), B_123), k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_subset_1(B_123, u1_struct_0(A_122)) | ~l1_orders_2(A_122) | ~v3_orders_2(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.17/1.48  tff(c_851, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_759, c_845])).
% 3.17/1.48  tff(c_854, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_40, c_851])).
% 3.17/1.48  tff(c_855, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_50, c_854])).
% 3.17/1.48  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.17/1.48  tff(c_762, plain, (r2_hidden('#skF_5', k2_orders_2('#skF_4', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_759, c_38])).
% 3.17/1.48  tff(c_894, plain, (![B_132, A_133, C_134]: (~r2_hidden(B_132, k2_orders_2(A_133, C_134)) | ~r2_hidden(B_132, C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~m1_subset_1(B_132, u1_struct_0(A_133)) | ~l1_orders_2(A_133) | ~v5_orders_2(A_133) | ~v4_orders_2(A_133) | ~v3_orders_2(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.17/1.48  tff(c_905, plain, (~r2_hidden('#skF_5', k1_tarski('#skF_5')) | ~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_762, c_894])).
% 3.17/1.48  tff(c_911, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_855, c_10, c_905])).
% 3.17/1.48  tff(c_913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_911])).
% 3.17/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.48  
% 3.17/1.48  Inference rules
% 3.17/1.48  ----------------------
% 3.17/1.48  #Ref     : 0
% 3.17/1.48  #Sup     : 179
% 3.17/1.48  #Fact    : 0
% 3.17/1.48  #Define  : 0
% 3.17/1.48  #Split   : 4
% 3.17/1.48  #Chain   : 0
% 3.17/1.48  #Close   : 0
% 3.17/1.48  
% 3.17/1.48  Ordering : KBO
% 3.17/1.48  
% 3.17/1.48  Simplification rules
% 3.17/1.48  ----------------------
% 3.17/1.48  #Subsume      : 19
% 3.17/1.48  #Demod        : 227
% 3.17/1.48  #Tautology    : 104
% 3.17/1.48  #SimpNegUnit  : 28
% 3.17/1.48  #BackRed      : 36
% 3.17/1.48  
% 3.17/1.48  #Partial instantiations: 0
% 3.17/1.48  #Strategies tried      : 1
% 3.17/1.48  
% 3.17/1.48  Timing (in seconds)
% 3.17/1.48  ----------------------
% 3.17/1.48  Preprocessing        : 0.32
% 3.17/1.48  Parsing              : 0.17
% 3.17/1.48  CNF conversion       : 0.02
% 3.17/1.48  Main loop            : 0.40
% 3.17/1.48  Inferencing          : 0.15
% 3.17/1.48  Reduction            : 0.13
% 3.17/1.48  Demodulation         : 0.08
% 3.17/1.48  BG Simplification    : 0.02
% 3.17/1.48  Subsumption          : 0.07
% 3.17/1.48  Abstraction          : 0.02
% 3.17/1.48  MUC search           : 0.00
% 3.17/1.49  Cooper               : 0.00
% 3.17/1.49  Total                : 0.75
% 3.17/1.49  Index Insertion      : 0.00
% 3.17/1.49  Index Deletion       : 0.00
% 3.17/1.49  Index Matching       : 0.00
% 3.17/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
