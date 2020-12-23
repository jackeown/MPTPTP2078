%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1476+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:57 EST 2020

% Result     : Theorem 18.07s
% Output     : CNFRefutation 18.44s
% Verified   : 
% Statistics : Number of formulae       :  347 (18285 expanded)
%              Number of leaves         :   43 (6198 expanded)
%              Depth                    :   36
%              Number of atoms          :  725 (48722 expanded)
%              Number of equality atoms :  239 (8859 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > l1_orders_2 > k3_relset_1 > k8_lattice3 > k4_tarski > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k4_relat_1 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(k7_lattice3,type,(
    k7_lattice3: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k8_lattice3,type,(
    k8_lattice3: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r1_orders_2(A,B,C)
                <=> r1_orders_2(k7_lattice3(A),k8_lattice3(A,C),k8_lattice3(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_lattice3)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k8_lattice3(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattice3)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(k7_lattice3(A))
        & l1_orders_2(k7_lattice3(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k8_lattice3(A,B),u1_struct_0(k7_lattice3(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_lattice3)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(A) = g1_orders_2(u1_struct_0(A),k3_relset_1(u1_struct_0(A),u1_struct_0(A),u1_orders_2(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_98,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_110,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_121,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_116,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_56,plain,
    ( ~ r1_orders_2(k7_lattice3('#skF_5'),k8_lattice3('#skF_5','#skF_7'),k8_lattice3('#skF_5','#skF_6'))
    | ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_88,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_54,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_99,plain,(
    ! [A_71,B_72] :
      ( k8_lattice3(A_71,B_72) = B_72
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l1_orders_2(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_105,plain,
    ( k8_lattice3('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_99])).

tff(c_111,plain,(
    k8_lattice3('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_105])).

tff(c_102,plain,
    ( k8_lattice3('#skF_5','#skF_7') = '#skF_7'
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_99])).

tff(c_108,plain,(
    k8_lattice3('#skF_5','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_102])).

tff(c_62,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r1_orders_2(k7_lattice3('#skF_5'),k8_lattice3('#skF_5','#skF_7'),k8_lattice3('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_135,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r1_orders_2(k7_lattice3('#skF_5'),'#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_108,c_62])).

tff(c_136,plain,(
    r1_orders_2(k7_lattice3('#skF_5'),'#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_135])).

tff(c_28,plain,(
    ! [A_34] :
      ( l1_orders_2(k7_lattice3(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_151,plain,(
    ! [A_80,B_81] :
      ( m1_subset_1(k8_lattice3(A_80,B_81),u1_struct_0(k7_lattice3(A_80)))
      | ~ m1_subset_1(B_81,u1_struct_0(A_80))
      | ~ l1_orders_2(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_157,plain,
    ( m1_subset_1('#skF_6',u1_struct_0(k7_lattice3('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_151])).

tff(c_163,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k7_lattice3('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_157])).

tff(c_8,plain,(
    ! [A_6,B_8] :
      ( k8_lattice3(A_6,B_8) = B_8
      | ~ m1_subset_1(B_8,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_169,plain,
    ( k8_lattice3(k7_lattice3('#skF_5'),'#skF_6') = '#skF_6'
    | ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(resolution,[status(thm)],[c_163,c_8])).

tff(c_183,plain,(
    ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_186,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_183])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_186])).

tff(c_192,plain,(
    l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_30,plain,(
    ! [A_34] :
      ( v1_orders_2(k7_lattice3(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    ! [A_37] :
      ( m1_subset_1(u1_orders_2(A_37),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_37),u1_struct_0(A_37))))
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [A_5] :
      ( g1_orders_2(u1_struct_0(A_5),k3_relset_1(u1_struct_0(A_5),u1_struct_0(A_5),u1_orders_2(A_5))) = k7_lattice3(A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_178,plain,(
    ! [C_82,A_83,D_84,B_85] :
      ( C_82 = A_83
      | g1_orders_2(C_82,D_84) != g1_orders_2(A_83,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_zfmisc_1(A_83,A_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_987,plain,(
    ! [A_172,C_173,D_174] :
      ( u1_struct_0(A_172) = C_173
      | g1_orders_2(C_173,D_174) != A_172
      | ~ m1_subset_1(u1_orders_2(A_172),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172),u1_struct_0(A_172))))
      | ~ v1_orders_2(A_172)
      | ~ l1_orders_2(A_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_1079,plain,(
    ! [A_191,A_190] :
      ( u1_struct_0(A_191) = u1_struct_0(A_190)
      | k7_lattice3(A_190) != A_191
      | ~ m1_subset_1(u1_orders_2(A_191),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191),u1_struct_0(A_191))))
      | ~ v1_orders_2(A_191)
      | ~ l1_orders_2(A_191)
      | ~ l1_orders_2(A_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_987])).

tff(c_1084,plain,(
    ! [A_193,A_192] :
      ( u1_struct_0(A_193) = u1_struct_0(A_192)
      | k7_lattice3(A_193) != A_192
      | ~ v1_orders_2(A_192)
      | ~ l1_orders_2(A_193)
      | ~ l1_orders_2(A_192) ) ),
    inference(resolution,[status(thm)],[c_34,c_1079])).

tff(c_1116,plain,(
    ! [A_194,A_195] :
      ( u1_struct_0(k7_lattice3(A_194)) = u1_struct_0(A_195)
      | k7_lattice3(A_195) != k7_lattice3(A_194)
      | ~ l1_orders_2(A_195)
      | ~ l1_orders_2(k7_lattice3(A_194))
      | ~ l1_orders_2(A_194) ) ),
    inference(resolution,[status(thm)],[c_30,c_1084])).

tff(c_1154,plain,(
    ! [A_199] :
      ( u1_struct_0(k7_lattice3(A_199)) = u1_struct_0('#skF_5')
      | k7_lattice3(A_199) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(k7_lattice3(A_199))
      | ~ l1_orders_2(A_199) ) ),
    inference(resolution,[status(thm)],[c_54,c_1116])).

tff(c_1178,plain,
    ( u1_struct_0(k7_lattice3('#skF_5')) = u1_struct_0('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_192,c_1154])).

tff(c_1205,plain,(
    u1_struct_0(k7_lattice3('#skF_5')) = u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1178])).

tff(c_1238,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3('#skF_5')),u1_struct_0('#skF_5'))))
    | ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1205,c_34])).

tff(c_1264,plain,(
    m1_subset_1(u1_orders_2(k7_lattice3('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_1205,c_1238])).

tff(c_4,plain,(
    ! [C_4,A_2,B_3] :
      ( v1_relat_1(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_2,B_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1465,plain,(
    v1_relat_1(u1_orders_2(k7_lattice3('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_1264,c_4])).

tff(c_129,plain,(
    ! [A_74] :
      ( m1_subset_1(u1_orders_2(A_74),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_74),u1_struct_0(A_74))))
      | ~ l1_orders_2(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_133,plain,(
    ! [A_74] :
      ( v1_relat_1(u1_orders_2(A_74))
      | ~ l1_orders_2(A_74) ) ),
    inference(resolution,[status(thm)],[c_129,c_4])).

tff(c_1241,plain,
    ( g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2(k7_lattice3('#skF_5'))) = k7_lattice3('#skF_5')
    | ~ v1_orders_2(k7_lattice3('#skF_5'))
    | ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1205,c_2])).

tff(c_1266,plain,
    ( g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2(k7_lattice3('#skF_5'))) = k7_lattice3('#skF_5')
    | ~ v1_orders_2(k7_lattice3('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_1241])).

tff(c_1505,plain,(
    ~ v1_orders_2(k7_lattice3('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1266])).

tff(c_1509,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_1505])).

tff(c_1513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1509])).

tff(c_1514,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2(k7_lattice3('#skF_5'))) = k7_lattice3('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1266])).

tff(c_137,plain,(
    ! [A_76,B_77,C_78] :
      ( k3_relset_1(A_76,B_77,C_78) = k4_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_141,plain,(
    ! [A_37] :
      ( k3_relset_1(u1_struct_0(A_37),u1_struct_0(A_37),u1_orders_2(A_37)) = k4_relat_1(u1_orders_2(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(resolution,[status(thm)],[c_34,c_137])).

tff(c_287,plain,(
    ! [A_90] :
      ( g1_orders_2(u1_struct_0(A_90),k3_relset_1(u1_struct_0(A_90),u1_struct_0(A_90),u1_orders_2(A_90))) = k7_lattice3(A_90)
      | ~ l1_orders_2(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_311,plain,(
    ! [A_91] :
      ( g1_orders_2(u1_struct_0(A_91),k4_relat_1(u1_orders_2(A_91))) = k7_lattice3(A_91)
      | ~ l1_orders_2(A_91)
      | ~ l1_orders_2(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_287])).

tff(c_36,plain,(
    ! [D_43,B_39,C_42,A_38] :
      ( D_43 = B_39
      | g1_orders_2(C_42,D_43) != g1_orders_2(A_38,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_316,plain,(
    ! [A_91,B_39,A_38] :
      ( k4_relat_1(u1_orders_2(A_91)) = B_39
      | k7_lattice3(A_91) != g1_orders_2(A_38,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k2_zfmisc_1(A_38,A_38)))
      | ~ l1_orders_2(A_91)
      | ~ l1_orders_2(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_36])).

tff(c_1531,plain,(
    ! [A_91] :
      ( u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2(A_91))
      | k7_lattice3(A_91) != k7_lattice3('#skF_5')
      | ~ m1_subset_1(u1_orders_2(k7_lattice3('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
      | ~ l1_orders_2(A_91)
      | ~ l1_orders_2(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1514,c_316])).

tff(c_5768,plain,(
    ! [A_294] :
      ( u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2(A_294))
      | k7_lattice3(A_294) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_294) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1264,c_1531])).

tff(c_40,plain,(
    ! [A_44] :
      ( k4_relat_1(k4_relat_1(A_44)) = A_44
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_8631,plain,(
    ! [A_354] :
      ( u1_orders_2(A_354) = k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))
      | ~ v1_relat_1(u1_orders_2(A_354))
      | k7_lattice3(A_354) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_354) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5768,c_40])).

tff(c_8659,plain,(
    ! [A_355] :
      ( u1_orders_2(A_355) = k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))
      | k7_lattice3(A_355) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_355) ) ),
    inference(resolution,[status(thm)],[c_133,c_8631])).

tff(c_8673,plain,(
    k4_relat_1(u1_orders_2(k7_lattice3('#skF_5'))) = u1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_8659])).

tff(c_8888,plain,
    ( u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2('#skF_5'))
    | ~ v1_relat_1(u1_orders_2(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8673,c_40])).

tff(c_8972,plain,(
    u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_8888])).

tff(c_438,plain,(
    ! [B_101,C_102,A_103] :
      ( r2_hidden(k4_tarski(B_101,C_102),u1_orders_2(A_103))
      | ~ r1_orders_2(A_103,B_101,C_102)
      | ~ m1_subset_1(C_102,u1_struct_0(A_103))
      | ~ m1_subset_1(B_101,u1_struct_0(A_103))
      | ~ l1_orders_2(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(A_48,B_49)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_449,plain,(
    ! [B_101,C_102,A_103] :
      ( m1_subset_1(k4_tarski(B_101,C_102),u1_orders_2(A_103))
      | ~ r1_orders_2(A_103,B_101,C_102)
      | ~ m1_subset_1(C_102,u1_struct_0(A_103))
      | ~ m1_subset_1(B_101,u1_struct_0(A_103))
      | ~ l1_orders_2(A_103) ) ),
    inference(resolution,[status(thm)],[c_438,c_44])).

tff(c_9191,plain,(
    ! [B_101,C_102] :
      ( m1_subset_1(k4_tarski(B_101,C_102),k4_relat_1(u1_orders_2('#skF_5')))
      | ~ r1_orders_2(k7_lattice3('#skF_5'),B_101,C_102)
      | ~ m1_subset_1(C_102,u1_struct_0(k7_lattice3('#skF_5')))
      | ~ m1_subset_1(B_101,u1_struct_0(k7_lattice3('#skF_5')))
      | ~ l1_orders_2(k7_lattice3('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8972,c_449])).

tff(c_30898,plain,(
    ! [B_642,C_643] :
      ( m1_subset_1(k4_tarski(B_642,C_643),k4_relat_1(u1_orders_2('#skF_5')))
      | ~ r1_orders_2(k7_lattice3('#skF_5'),B_642,C_643)
      | ~ m1_subset_1(C_643,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_642,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_1205,c_1205,c_9191])).

tff(c_160,plain,
    ( m1_subset_1('#skF_7',u1_struct_0(k7_lattice3('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_151])).

tff(c_165,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k7_lattice3('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_160])).

tff(c_48,plain,(
    ! [B_53,A_52] :
      ( ~ v1_xboole_0(B_53)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_482,plain,(
    ! [A_113,B_114,C_115] :
      ( ~ v1_xboole_0(u1_orders_2(A_113))
      | ~ r1_orders_2(A_113,B_114,C_115)
      | ~ m1_subset_1(C_115,u1_struct_0(A_113))
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_orders_2(A_113) ) ),
    inference(resolution,[status(thm)],[c_438,c_48])).

tff(c_484,plain,
    ( ~ v1_xboole_0(u1_orders_2(k7_lattice3('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0(k7_lattice3('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(resolution,[status(thm)],[c_136,c_482])).

tff(c_487,plain,(
    ~ v1_xboole_0(u1_orders_2(k7_lattice3('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_165,c_163,c_484])).

tff(c_9123,plain,(
    ~ v1_xboole_0(k4_relat_1(u1_orders_2('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8972,c_487])).

tff(c_173,plain,
    ( k8_lattice3(k7_lattice3('#skF_5'),'#skF_7') = '#skF_7'
    | ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(resolution,[status(thm)],[c_165,c_8])).

tff(c_194,plain,(
    k8_lattice3(k7_lattice3('#skF_5'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_173])).

tff(c_32,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k8_lattice3(A_35,B_36),u1_struct_0(k7_lattice3(A_35)))
      | ~ m1_subset_1(B_36,u1_struct_0(A_35))
      | ~ l1_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_198,plain,
    ( m1_subset_1('#skF_7',u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))))
    | ~ m1_subset_1('#skF_7',u1_struct_0(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_32])).

tff(c_202,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k7_lattice3(k7_lattice3('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_165,c_198])).

tff(c_216,plain,
    ( k8_lattice3(k7_lattice3(k7_lattice3('#skF_5')),'#skF_7') = '#skF_7'
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_202,c_8])).

tff(c_221,plain,(
    ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_224,plain,(
    ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(resolution,[status(thm)],[c_28,c_221])).

tff(c_228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_224])).

tff(c_230,plain,(
    l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_229,plain,(
    k8_lattice3(k7_lattice3(k7_lattice3('#skF_5')),'#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_243,plain,
    ( m1_subset_1('#skF_7',u1_struct_0(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))))
    | ~ m1_subset_1('#skF_7',u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_32])).

tff(c_247,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_202,c_243])).

tff(c_252,plain,
    ( k8_lattice3(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))),'#skF_7') = '#skF_7'
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_247,c_8])).

tff(c_268,plain,(
    ~ l1_orders_2(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_271,plain,(
    ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_28,c_268])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_271])).

tff(c_277,plain,(
    l1_orders_2(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_1172,plain,
    ( u1_struct_0(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))) = u1_struct_0('#skF_5')
    | k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) != k7_lattice3('#skF_5')
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_277,c_1154])).

tff(c_1199,plain,
    ( u1_struct_0(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))) = u1_struct_0('#skF_5')
    | k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) != k7_lattice3('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_1172])).

tff(c_1709,plain,(
    k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) != k7_lattice3('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1199])).

tff(c_1799,plain,(
    ! [A_215] :
      ( u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2(A_215))
      | k7_lattice3(A_215) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1264,c_1531])).

tff(c_3529,plain,(
    ! [A_254] :
      ( u1_orders_2(A_254) = k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))
      | ~ v1_relat_1(u1_orders_2(A_254))
      | k7_lattice3(A_254) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_254) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1799,c_40])).

tff(c_3547,plain,(
    ! [A_255] :
      ( u1_orders_2(A_255) = k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))
      | k7_lattice3(A_255) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_255) ) ),
    inference(resolution,[status(thm)],[c_133,c_3529])).

tff(c_3577,plain,(
    k4_relat_1(u1_orders_2(k7_lattice3('#skF_5'))) = u1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_3547])).

tff(c_3648,plain,
    ( u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2('#skF_5'))
    | ~ v1_relat_1(u1_orders_2(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3577,c_40])).

tff(c_3705,plain,(
    u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_3648])).

tff(c_3801,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2('#skF_5'))) = k7_lattice3('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3705,c_1514])).

tff(c_304,plain,(
    ! [A_37] :
      ( g1_orders_2(u1_struct_0(A_37),k4_relat_1(u1_orders_2(A_37))) = k7_lattice3(A_37)
      | ~ l1_orders_2(A_37)
      | ~ l1_orders_2(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_287])).

tff(c_1214,plain,
    ( g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))) = k7_lattice3(k7_lattice3('#skF_5'))
    | ~ l1_orders_2(k7_lattice3('#skF_5'))
    | ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1205,c_304])).

tff(c_1248,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))) = k7_lattice3(k7_lattice3('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_192,c_1214])).

tff(c_38,plain,(
    ! [C_42,A_38,D_43,B_39] :
      ( C_42 = A_38
      | g1_orders_2(C_42,D_43) != g1_orders_2(A_38,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2379,plain,(
    ! [A_229,B_230] :
      ( u1_struct_0('#skF_5') = A_229
      | k7_lattice3(k7_lattice3('#skF_5')) != g1_orders_2(A_229,B_230)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(k2_zfmisc_1(A_229,A_229))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1248,c_38])).

tff(c_2409,plain,(
    ! [A_231] :
      ( u1_struct_0(A_231) = u1_struct_0('#skF_5')
      | g1_orders_2(u1_struct_0(A_231),u1_orders_2(A_231)) != k7_lattice3(k7_lattice3('#skF_5'))
      | ~ l1_orders_2(A_231) ) ),
    inference(resolution,[status(thm)],[c_34,c_2379])).

tff(c_2424,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_5')
      | k7_lattice3(k7_lattice3('#skF_5')) != A_1
      | ~ l1_orders_2(A_1)
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2409])).

tff(c_2445,plain,
    ( u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))) = u1_struct_0('#skF_5')
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))
    | ~ v1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2424])).

tff(c_2447,plain,
    ( u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))) = u1_struct_0('#skF_5')
    | ~ v1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_230,c_2445])).

tff(c_2449,plain,(
    ~ v1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_2447])).

tff(c_2452,plain,(
    ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(resolution,[status(thm)],[c_30,c_2449])).

tff(c_2456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_2452])).

tff(c_2458,plain,(
    v1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_2447])).

tff(c_2457,plain,(
    u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))) = u1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_2447])).

tff(c_2547,plain,
    ( g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))) = k7_lattice3(k7_lattice3('#skF_5'))
    | ~ v1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2457,c_2])).

tff(c_2584,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))) = k7_lattice3(k7_lattice3('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_2458,c_2547])).

tff(c_2541,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))))))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2457,c_34])).

tff(c_2580,plain,(
    m1_subset_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_2457,c_2541])).

tff(c_3580,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) = k7_lattice3(k7_lattice3('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3577,c_1248])).

tff(c_5527,plain,(
    ! [B_289,A_290] :
      ( u1_orders_2('#skF_5') = B_289
      | k7_lattice3(k7_lattice3('#skF_5')) != g1_orders_2(A_290,B_289)
      | ~ m1_subset_1(B_289,k1_zfmisc_1(k2_zfmisc_1(A_290,A_290))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3580,c_36])).

tff(c_5533,plain,
    ( u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) = u1_orders_2('#skF_5')
    | g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))) != k7_lattice3(k7_lattice3('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2580,c_5527])).

tff(c_5557,plain,(
    u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) = u1_orders_2('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2584,c_5533])).

tff(c_2520,plain,
    ( g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))))) = k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2457,c_304])).

tff(c_2566,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))))) = k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_230,c_2520])).

tff(c_5564,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2('#skF_5'))) = k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5557,c_2566])).

tff(c_5568,plain,(
    k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) = k7_lattice3('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3801,c_5564])).

tff(c_5570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1709,c_5568])).

tff(c_5572,plain,(
    k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) = k7_lattice3('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1199])).

tff(c_1515,plain,(
    v1_orders_2(k7_lattice3('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1266])).

tff(c_1082,plain,(
    ! [A_37,A_190] :
      ( u1_struct_0(A_37) = u1_struct_0(A_190)
      | k7_lattice3(A_190) != A_37
      | ~ v1_orders_2(A_37)
      | ~ l1_orders_2(A_190)
      | ~ l1_orders_2(A_37) ) ),
    inference(resolution,[status(thm)],[c_34,c_1079])).

tff(c_1517,plain,(
    ! [A_190] :
      ( u1_struct_0(k7_lattice3('#skF_5')) = u1_struct_0(A_190)
      | k7_lattice3(A_190) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_190)
      | ~ l1_orders_2(k7_lattice3('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1515,c_1082])).

tff(c_1666,plain,(
    ! [A_211] :
      ( u1_struct_0(A_211) = u1_struct_0('#skF_5')
      | k7_lattice3(A_211) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_1205,c_1517])).

tff(c_1703,plain,
    ( u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))) = u1_struct_0('#skF_5')
    | k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) != k7_lattice3('#skF_5') ),
    inference(resolution,[status(thm)],[c_230,c_1666])).

tff(c_6042,plain,(
    u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))) = u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5572,c_1703])).

tff(c_6077,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))))))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6042,c_34])).

tff(c_6115,plain,(
    m1_subset_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_6042,c_6077])).

tff(c_6393,plain,(
    v1_relat_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_6115,c_4])).

tff(c_6056,plain,
    ( g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))))) = k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6042,c_304])).

tff(c_6101,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))))) = k7_lattice3('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_230,c_5572,c_6056])).

tff(c_1541,plain,(
    ! [D_43,C_42] :
      ( u1_orders_2(k7_lattice3('#skF_5')) = D_43
      | g1_orders_2(C_42,D_43) != k7_lattice3('#skF_5')
      | ~ m1_subset_1(u1_orders_2(k7_lattice3('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1514,c_36])).

tff(c_1559,plain,(
    ! [D_43,C_42] :
      ( u1_orders_2(k7_lattice3('#skF_5')) = D_43
      | g1_orders_2(C_42,D_43) != k7_lattice3('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1264,c_1541])).

tff(c_6163,plain,(
    k4_relat_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))) = u1_orders_2(k7_lattice3('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6101,c_1559])).

tff(c_6220,plain,
    ( u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) = k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))
    | ~ v1_relat_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6163,c_40])).

tff(c_6517,plain,(
    u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) = k4_relat_1(u1_orders_2(k7_lattice3('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6393,c_6220])).

tff(c_6519,plain,(
    v1_relat_1(k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6517,c_6393])).

tff(c_8781,plain,(
    v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8673,c_6519])).

tff(c_9121,plain,(
    v1_relat_1(k4_relat_1(u1_orders_2('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8972,c_1465])).

tff(c_1551,plain,(
    ! [A_91] :
      ( u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2(A_91))
      | k7_lattice3(A_91) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1264,c_1531])).

tff(c_10449,plain,(
    ! [A_375] :
      ( k4_relat_1(u1_orders_2(A_375)) = k4_relat_1(u1_orders_2('#skF_5'))
      | k7_lattice3(A_375) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8972,c_1551])).

tff(c_46,plain,(
    ! [A_50,B_51] :
      ( r2_hidden(A_50,B_51)
      | v1_xboole_0(B_51)
      | ~ m1_subset_1(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_366,plain,(
    ! [D_92,C_93,A_94] :
      ( r2_hidden(k4_tarski(D_92,C_93),A_94)
      | ~ r2_hidden(k4_tarski(C_93,D_92),k4_relat_1(A_94))
      | ~ v1_relat_1(k4_relat_1(A_94))
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_373,plain,(
    ! [D_92,C_93,A_94] :
      ( r2_hidden(k4_tarski(D_92,C_93),A_94)
      | ~ v1_relat_1(k4_relat_1(A_94))
      | ~ v1_relat_1(A_94)
      | v1_xboole_0(k4_relat_1(A_94))
      | ~ m1_subset_1(k4_tarski(C_93,D_92),k4_relat_1(A_94)) ) ),
    inference(resolution,[status(thm)],[c_46,c_366])).

tff(c_10616,plain,(
    ! [D_92,C_93,A_375] :
      ( r2_hidden(k4_tarski(D_92,C_93),u1_orders_2('#skF_5'))
      | ~ v1_relat_1(k4_relat_1(u1_orders_2('#skF_5')))
      | ~ v1_relat_1(u1_orders_2('#skF_5'))
      | v1_xboole_0(k4_relat_1(u1_orders_2('#skF_5')))
      | ~ m1_subset_1(k4_tarski(C_93,D_92),k4_relat_1(u1_orders_2(A_375)))
      | k7_lattice3(A_375) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_375) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10449,c_373])).

tff(c_10744,plain,(
    ! [D_92,C_93,A_375] :
      ( r2_hidden(k4_tarski(D_92,C_93),u1_orders_2('#skF_5'))
      | v1_xboole_0(k4_relat_1(u1_orders_2('#skF_5')))
      | ~ m1_subset_1(k4_tarski(C_93,D_92),k4_relat_1(u1_orders_2(A_375)))
      | k7_lattice3(A_375) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8781,c_9121,c_10616])).

tff(c_10745,plain,(
    ! [D_92,C_93,A_375] :
      ( r2_hidden(k4_tarski(D_92,C_93),u1_orders_2('#skF_5'))
      | ~ m1_subset_1(k4_tarski(C_93,D_92),k4_relat_1(u1_orders_2(A_375)))
      | k7_lattice3(A_375) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_375) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9123,c_10744])).

tff(c_30907,plain,(
    ! [C_643,B_642] :
      ( r2_hidden(k4_tarski(C_643,B_642),u1_orders_2('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_orders_2(k7_lattice3('#skF_5'),B_642,C_643)
      | ~ m1_subset_1(C_643,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_642,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_30898,c_10745])).

tff(c_30953,plain,(
    ! [C_644,B_645] :
      ( r2_hidden(k4_tarski(C_644,B_645),u1_orders_2('#skF_5'))
      | ~ r1_orders_2(k7_lattice3('#skF_5'),B_645,C_644)
      | ~ m1_subset_1(C_644,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_645,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_30907])).

tff(c_22,plain,(
    ! [A_26,B_30,C_32] :
      ( r1_orders_2(A_26,B_30,C_32)
      | ~ r2_hidden(k4_tarski(B_30,C_32),u1_orders_2(A_26))
      | ~ m1_subset_1(C_32,u1_struct_0(A_26))
      | ~ m1_subset_1(B_30,u1_struct_0(A_26))
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30995,plain,(
    ! [C_644,B_645] :
      ( r1_orders_2('#skF_5',C_644,B_645)
      | ~ l1_orders_2('#skF_5')
      | ~ r1_orders_2(k7_lattice3('#skF_5'),B_645,C_644)
      | ~ m1_subset_1(C_644,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_645,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_30953,c_22])).

tff(c_31044,plain,(
    ! [C_646,B_647] :
      ( r1_orders_2('#skF_5',C_646,B_647)
      | ~ r1_orders_2(k7_lattice3('#skF_5'),B_647,C_646)
      | ~ m1_subset_1(C_646,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_647,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_30995])).

tff(c_31058,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_136,c_31044])).

tff(c_31068,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_31058])).

tff(c_31070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_31068])).

tff(c_31072,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_24,plain,(
    ! [B_30,C_32,A_26] :
      ( r2_hidden(k4_tarski(B_30,C_32),u1_orders_2(A_26))
      | ~ r1_orders_2(A_26,B_30,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_26))
      | ~ m1_subset_1(B_30,u1_struct_0(A_26))
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_31117,plain,(
    ! [A_656] :
      ( m1_subset_1(u1_orders_2(A_656),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_656),u1_struct_0(A_656))))
      | ~ l1_orders_2(A_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_31121,plain,(
    ! [A_656] :
      ( v1_relat_1(u1_orders_2(A_656))
      | ~ l1_orders_2(A_656) ) ),
    inference(resolution,[status(thm)],[c_31117,c_4])).

tff(c_31094,plain,(
    ! [A_654,B_655] :
      ( k8_lattice3(A_654,B_655) = B_655
      | ~ m1_subset_1(B_655,u1_struct_0(A_654))
      | ~ l1_orders_2(A_654) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_31100,plain,
    ( k8_lattice3('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_31094])).

tff(c_31106,plain,(
    k8_lattice3('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_31100])).

tff(c_31137,plain,(
    ! [A_662,B_663] :
      ( m1_subset_1(k8_lattice3(A_662,B_663),u1_struct_0(k7_lattice3(A_662)))
      | ~ m1_subset_1(B_663,u1_struct_0(A_662))
      | ~ l1_orders_2(A_662) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_31143,plain,
    ( m1_subset_1('#skF_6',u1_struct_0(k7_lattice3('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_31106,c_31137])).

tff(c_31149,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k7_lattice3('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_31143])).

tff(c_31155,plain,
    ( k8_lattice3(k7_lattice3('#skF_5'),'#skF_6') = '#skF_6'
    | ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(resolution,[status(thm)],[c_31149,c_8])).

tff(c_31160,plain,(
    ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_31155])).

tff(c_31163,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_31160])).

tff(c_31167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_31163])).

tff(c_31169,plain,(
    l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_31155])).

tff(c_31237,plain,(
    ! [C_665,A_666,D_667,B_668] :
      ( C_665 = A_666
      | g1_orders_2(C_665,D_667) != g1_orders_2(A_666,B_668)
      | ~ m1_subset_1(B_668,k1_zfmisc_1(k2_zfmisc_1(A_666,A_666))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_31743,plain,(
    ! [A_727,C_728,D_729] :
      ( u1_struct_0(A_727) = C_728
      | g1_orders_2(C_728,D_729) != A_727
      | ~ m1_subset_1(u1_orders_2(A_727),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_727),u1_struct_0(A_727))))
      | ~ v1_orders_2(A_727)
      | ~ l1_orders_2(A_727) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_31237])).

tff(c_32119,plain,(
    ! [A_773,A_772] :
      ( u1_struct_0(A_773) = u1_struct_0(A_772)
      | k7_lattice3(A_773) != A_772
      | ~ m1_subset_1(u1_orders_2(A_772),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_772),u1_struct_0(A_772))))
      | ~ v1_orders_2(A_772)
      | ~ l1_orders_2(A_772)
      | ~ l1_orders_2(A_773) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_31743])).

tff(c_32124,plain,(
    ! [A_775,A_774] :
      ( u1_struct_0(A_775) = u1_struct_0(A_774)
      | k7_lattice3(A_774) != A_775
      | ~ v1_orders_2(A_775)
      | ~ l1_orders_2(A_774)
      | ~ l1_orders_2(A_775) ) ),
    inference(resolution,[status(thm)],[c_34,c_32119])).

tff(c_32128,plain,(
    ! [A_776,A_777] :
      ( u1_struct_0(k7_lattice3(A_776)) = u1_struct_0(A_777)
      | k7_lattice3(A_777) != k7_lattice3(A_776)
      | ~ l1_orders_2(A_777)
      | ~ l1_orders_2(k7_lattice3(A_776))
      | ~ l1_orders_2(A_776) ) ),
    inference(resolution,[status(thm)],[c_30,c_32124])).

tff(c_32159,plain,(
    ! [A_778] :
      ( u1_struct_0(k7_lattice3(A_778)) = u1_struct_0('#skF_5')
      | k7_lattice3(A_778) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(k7_lattice3(A_778))
      | ~ l1_orders_2(A_778) ) ),
    inference(resolution,[status(thm)],[c_54,c_32128])).

tff(c_32183,plain,
    ( u1_struct_0(k7_lattice3('#skF_5')) = u1_struct_0('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_31169,c_32159])).

tff(c_32210,plain,(
    u1_struct_0(k7_lattice3('#skF_5')) = u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_32183])).

tff(c_32240,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k7_lattice3('#skF_5')))))
    | ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32210,c_34])).

tff(c_32267,plain,(
    m1_subset_1(u1_orders_2(k7_lattice3('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31169,c_32210,c_32240])).

tff(c_32249,plain,
    ( g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2(k7_lattice3('#skF_5'))) = k7_lattice3('#skF_5')
    | ~ v1_orders_2(k7_lattice3('#skF_5'))
    | ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32210,c_2])).

tff(c_32273,plain,
    ( g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2(k7_lattice3('#skF_5'))) = k7_lattice3('#skF_5')
    | ~ v1_orders_2(k7_lattice3('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31169,c_32249])).

tff(c_32506,plain,(
    ~ v1_orders_2(k7_lattice3('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_32273])).

tff(c_32509,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_32506])).

tff(c_32513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_32509])).

tff(c_32514,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2(k7_lattice3('#skF_5'))) = k7_lattice3('#skF_5') ),
    inference(splitRight,[status(thm)],[c_32273])).

tff(c_31123,plain,(
    ! [A_658,B_659,C_660] :
      ( k3_relset_1(A_658,B_659,C_660) = k4_relat_1(C_660)
      | ~ m1_subset_1(C_660,k1_zfmisc_1(k2_zfmisc_1(A_658,B_659))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_31127,plain,(
    ! [A_37] :
      ( k3_relset_1(u1_struct_0(A_37),u1_struct_0(A_37),u1_orders_2(A_37)) = k4_relat_1(u1_orders_2(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(resolution,[status(thm)],[c_34,c_31123])).

tff(c_31170,plain,(
    ! [A_664] :
      ( g1_orders_2(u1_struct_0(A_664),k3_relset_1(u1_struct_0(A_664),u1_struct_0(A_664),u1_orders_2(A_664))) = k7_lattice3(A_664)
      | ~ l1_orders_2(A_664) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_31179,plain,(
    ! [A_37] :
      ( g1_orders_2(u1_struct_0(A_37),k4_relat_1(u1_orders_2(A_37))) = k7_lattice3(A_37)
      | ~ l1_orders_2(A_37)
      | ~ l1_orders_2(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31127,c_31170])).

tff(c_31312,plain,(
    ! [D_670,B_671,C_672,A_673] :
      ( D_670 = B_671
      | g1_orders_2(C_672,D_670) != g1_orders_2(A_673,B_671)
      | ~ m1_subset_1(B_671,k1_zfmisc_1(k2_zfmisc_1(A_673,A_673))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_31314,plain,(
    ! [A_37,B_671,A_673] :
      ( k4_relat_1(u1_orders_2(A_37)) = B_671
      | k7_lattice3(A_37) != g1_orders_2(A_673,B_671)
      | ~ m1_subset_1(B_671,k1_zfmisc_1(k2_zfmisc_1(A_673,A_673)))
      | ~ l1_orders_2(A_37)
      | ~ l1_orders_2(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31179,c_31312])).

tff(c_32531,plain,(
    ! [A_37] :
      ( u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2(A_37))
      | k7_lattice3(A_37) != k7_lattice3('#skF_5')
      | ~ m1_subset_1(u1_orders_2(k7_lattice3('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
      | ~ l1_orders_2(A_37)
      | ~ l1_orders_2(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32514,c_31314])).

tff(c_36954,plain,(
    ! [A_885] :
      ( u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2(A_885))
      | k7_lattice3(A_885) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_885) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32267,c_32531])).

tff(c_38998,plain,(
    ! [A_929] :
      ( u1_orders_2(A_929) = k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))
      | ~ v1_relat_1(u1_orders_2(A_929))
      | k7_lattice3(A_929) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_929) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36954,c_40])).

tff(c_39069,plain,(
    ! [A_932] :
      ( u1_orders_2(A_932) = k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))
      | k7_lattice3(A_932) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_932) ) ),
    inference(resolution,[status(thm)],[c_31121,c_38998])).

tff(c_39083,plain,(
    k4_relat_1(u1_orders_2(k7_lattice3('#skF_5'))) = u1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_39069])).

tff(c_31168,plain,(
    k8_lattice3(k7_lattice3('#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_31155])).

tff(c_31185,plain,
    ( m1_subset_1('#skF_6',u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))))
    | ~ m1_subset_1('#skF_6',u1_struct_0(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31168,c_32])).

tff(c_31189,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k7_lattice3(k7_lattice3('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31169,c_31149,c_31185])).

tff(c_31194,plain,
    ( k8_lattice3(k7_lattice3(k7_lattice3('#skF_5')),'#skF_6') = '#skF_6'
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_31189,c_8])).

tff(c_31210,plain,(
    ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_31194])).

tff(c_31213,plain,(
    ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(resolution,[status(thm)],[c_28,c_31210])).

tff(c_31217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31169,c_31213])).

tff(c_31219,plain,(
    l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_31194])).

tff(c_31097,plain,
    ( k8_lattice3('#skF_5','#skF_7') = '#skF_7'
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_31094])).

tff(c_31103,plain,(
    k8_lattice3('#skF_5','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_31097])).

tff(c_31146,plain,
    ( m1_subset_1('#skF_7',u1_struct_0(k7_lattice3('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_31103,c_31137])).

tff(c_31151,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k7_lattice3('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_31146])).

tff(c_31159,plain,
    ( k8_lattice3(k7_lattice3('#skF_5'),'#skF_7') = '#skF_7'
    | ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(resolution,[status(thm)],[c_31151,c_8])).

tff(c_31196,plain,(
    k8_lattice3(k7_lattice3('#skF_5'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31169,c_31159])).

tff(c_31200,plain,
    ( m1_subset_1('#skF_7',u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))))
    | ~ m1_subset_1('#skF_7',u1_struct_0(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31196,c_32])).

tff(c_31204,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k7_lattice3(k7_lattice3('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31169,c_31151,c_31200])).

tff(c_31209,plain,
    ( k8_lattice3(k7_lattice3(k7_lattice3('#skF_5')),'#skF_7') = '#skF_7'
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_31204,c_8])).

tff(c_31247,plain,(
    k8_lattice3(k7_lattice3(k7_lattice3('#skF_5')),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31219,c_31209])).

tff(c_31251,plain,
    ( m1_subset_1('#skF_7',u1_struct_0(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))))
    | ~ m1_subset_1('#skF_7',u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_31247,c_32])).

tff(c_31255,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31219,c_31204,c_31251])).

tff(c_31260,plain,
    ( k8_lattice3(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))),'#skF_7') = '#skF_7'
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_31255,c_8])).

tff(c_31274,plain,(
    ~ l1_orders_2(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_31260])).

tff(c_31277,plain,(
    ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_28,c_31274])).

tff(c_31281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31219,c_31277])).

tff(c_31283,plain,(
    l1_orders_2(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_31260])).

tff(c_32177,plain,
    ( u1_struct_0(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))) = u1_struct_0('#skF_5')
    | k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) != k7_lattice3('#skF_5')
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_31283,c_32159])).

tff(c_32204,plain,
    ( u1_struct_0(k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))) = u1_struct_0('#skF_5')
    | k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) != k7_lattice3('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31219,c_32177])).

tff(c_32709,plain,(
    k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) != k7_lattice3('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_32204])).

tff(c_32358,plain,(
    v1_relat_1(u1_orders_2(k7_lattice3('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_32267,c_4])).

tff(c_32743,plain,(
    ! [A_795] :
      ( u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2(A_795))
      | k7_lattice3(A_795) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_795) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32267,c_32531])).

tff(c_34562,plain,(
    ! [A_835] :
      ( u1_orders_2(A_835) = k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))
      | ~ v1_relat_1(u1_orders_2(A_835))
      | k7_lattice3(A_835) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_835) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32743,c_40])).

tff(c_34580,plain,(
    ! [A_836] :
      ( u1_orders_2(A_836) = k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))
      | k7_lattice3(A_836) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_836) ) ),
    inference(resolution,[status(thm)],[c_31121,c_34562])).

tff(c_34610,plain,(
    k4_relat_1(u1_orders_2(k7_lattice3('#skF_5'))) = u1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_34580])).

tff(c_34674,plain,
    ( u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2('#skF_5'))
    | ~ v1_relat_1(u1_orders_2(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_34610,c_40])).

tff(c_34726,plain,(
    u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32358,c_34674])).

tff(c_34818,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2('#skF_5'))) = k7_lattice3('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34726,c_32514])).

tff(c_32219,plain,
    ( g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))) = k7_lattice3(k7_lattice3('#skF_5'))
    | ~ l1_orders_2(k7_lattice3('#skF_5'))
    | ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32210,c_31179])).

tff(c_32253,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))) = k7_lattice3(k7_lattice3('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31169,c_31169,c_32219])).

tff(c_33381,plain,(
    ! [A_808,B_809] :
      ( u1_struct_0('#skF_5') = A_808
      | k7_lattice3(k7_lattice3('#skF_5')) != g1_orders_2(A_808,B_809)
      | ~ m1_subset_1(B_809,k1_zfmisc_1(k2_zfmisc_1(A_808,A_808))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32253,c_38])).

tff(c_33424,plain,(
    ! [A_812] :
      ( u1_struct_0(A_812) = u1_struct_0('#skF_5')
      | g1_orders_2(u1_struct_0(A_812),u1_orders_2(A_812)) != k7_lattice3(k7_lattice3('#skF_5'))
      | ~ l1_orders_2(A_812) ) ),
    inference(resolution,[status(thm)],[c_34,c_33381])).

tff(c_33439,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_5')
      | k7_lattice3(k7_lattice3('#skF_5')) != A_1
      | ~ l1_orders_2(A_1)
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_33424])).

tff(c_33447,plain,
    ( u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))) = u1_struct_0('#skF_5')
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))
    | ~ v1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_33439])).

tff(c_33449,plain,
    ( u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))) = u1_struct_0('#skF_5')
    | ~ v1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31219,c_31219,c_33447])).

tff(c_33451,plain,(
    ~ v1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_33449])).

tff(c_33483,plain,(
    ~ l1_orders_2(k7_lattice3('#skF_5')) ),
    inference(resolution,[status(thm)],[c_30,c_33451])).

tff(c_33487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31169,c_33483])).

tff(c_33489,plain,(
    v1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_33449])).

tff(c_33488,plain,(
    u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))) = u1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_33449])).

tff(c_33552,plain,
    ( g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))) = k7_lattice3(k7_lattice3('#skF_5'))
    | ~ v1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_33488,c_2])).

tff(c_33588,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))) = k7_lattice3(k7_lattice3('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31219,c_33489,c_33552])).

tff(c_33546,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))),u1_struct_0('#skF_5'))))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_33488,c_34])).

tff(c_33584,plain,(
    m1_subset_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31219,c_33488,c_33546])).

tff(c_34613,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) = k7_lattice3(k7_lattice3('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34610,c_32253])).

tff(c_36646,plain,(
    ! [B_877,A_878] :
      ( u1_orders_2('#skF_5') = B_877
      | k7_lattice3(k7_lattice3('#skF_5')) != g1_orders_2(A_878,B_877)
      | ~ m1_subset_1(B_877,k1_zfmisc_1(k2_zfmisc_1(A_878,A_878))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34613,c_36])).

tff(c_36652,plain,
    ( u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) = u1_orders_2('#skF_5')
    | g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))) != k7_lattice3(k7_lattice3('#skF_5')) ),
    inference(resolution,[status(thm)],[c_33584,c_36646])).

tff(c_36676,plain,(
    u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) = u1_orders_2('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33588,c_36652])).

tff(c_33522,plain,
    ( g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))))) = k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_33488,c_31179])).

tff(c_33568,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))))) = k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31219,c_31219,c_33522])).

tff(c_36772,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2('#skF_5'))) = k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36676,c_33568])).

tff(c_36776,plain,(
    k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) = k7_lattice3('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34818,c_36772])).

tff(c_36778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32709,c_36776])).

tff(c_36780,plain,(
    k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) = k7_lattice3('#skF_5') ),
    inference(splitRight,[status(thm)],[c_32204])).

tff(c_31239,plain,(
    ! [A_5,A_666,B_668] :
      ( u1_struct_0(A_5) = A_666
      | k7_lattice3(A_5) != g1_orders_2(A_666,B_668)
      | ~ m1_subset_1(B_668,k1_zfmisc_1(k2_zfmisc_1(A_666,A_666)))
      | ~ l1_orders_2(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_31237])).

tff(c_32537,plain,(
    ! [A_5] :
      ( u1_struct_0(A_5) = u1_struct_0('#skF_5')
      | k7_lattice3(A_5) != k7_lattice3('#skF_5')
      | ~ m1_subset_1(u1_orders_2(k7_lattice3('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
      | ~ l1_orders_2(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32514,c_31239])).

tff(c_32666,plain,(
    ! [A_791] :
      ( u1_struct_0(A_791) = u1_struct_0('#skF_5')
      | k7_lattice3(A_791) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_791) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32267,c_32537])).

tff(c_32703,plain,
    ( u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))) = u1_struct_0('#skF_5')
    | k7_lattice3(k7_lattice3(k7_lattice3('#skF_5'))) != k7_lattice3('#skF_5') ),
    inference(resolution,[status(thm)],[c_31219,c_32666])).

tff(c_37168,plain,(
    u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))) = u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36780,c_32703])).

tff(c_37203,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3('#skF_5'))),u1_struct_0('#skF_5'))))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_37168,c_34])).

tff(c_37234,plain,(
    m1_subset_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31219,c_37168,c_37203])).

tff(c_37454,plain,(
    v1_relat_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_37234,c_4])).

tff(c_37179,plain,
    ( g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))))) = k7_lattice3(k7_lattice3(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_37168,c_31179])).

tff(c_37218,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),k4_relat_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))))) = k7_lattice3('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31219,c_31219,c_36780,c_37179])).

tff(c_32541,plain,(
    ! [D_43,C_42] :
      ( u1_orders_2(k7_lattice3('#skF_5')) = D_43
      | g1_orders_2(C_42,D_43) != k7_lattice3('#skF_5')
      | ~ m1_subset_1(u1_orders_2(k7_lattice3('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32514,c_36])).

tff(c_32559,plain,(
    ! [D_43,C_42] :
      ( u1_orders_2(k7_lattice3('#skF_5')) = D_43
      | g1_orders_2(C_42,D_43) != k7_lattice3('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32267,c_32541])).

tff(c_37277,plain,(
    k4_relat_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))) = u1_orders_2(k7_lattice3('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_37218,c_32559])).

tff(c_37318,plain,
    ( u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) = k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))
    | ~ v1_relat_1(u1_orders_2(k7_lattice3(k7_lattice3('#skF_5')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_37277,c_40])).

tff(c_37787,plain,(
    u1_orders_2(k7_lattice3(k7_lattice3('#skF_5'))) = k4_relat_1(u1_orders_2(k7_lattice3('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37454,c_37318])).

tff(c_37789,plain,(
    v1_relat_1(k4_relat_1(u1_orders_2(k7_lattice3('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37787,c_37454])).

tff(c_39088,plain,(
    v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39083,c_37789])).

tff(c_39177,plain,
    ( u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2('#skF_5'))
    | ~ v1_relat_1(u1_orders_2(k7_lattice3('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_39083,c_40])).

tff(c_39247,plain,(
    u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32358,c_39177])).

tff(c_39367,plain,(
    v1_relat_1(k4_relat_1(u1_orders_2('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39247,c_32358])).

tff(c_32551,plain,(
    ! [A_37] :
      ( u1_orders_2(k7_lattice3('#skF_5')) = k4_relat_1(u1_orders_2(A_37))
      | k7_lattice3(A_37) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32267,c_32531])).

tff(c_40469,plain,(
    ! [A_949] :
      ( k4_relat_1(u1_orders_2(A_949)) = k4_relat_1(u1_orders_2('#skF_5'))
      | k7_lattice3(A_949) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_949) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39247,c_32551])).

tff(c_20,plain,(
    ! [C_24,D_25,A_9] :
      ( r2_hidden(k4_tarski(C_24,D_25),k4_relat_1(A_9))
      | ~ r2_hidden(k4_tarski(D_25,C_24),A_9)
      | ~ v1_relat_1(k4_relat_1(A_9))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40647,plain,(
    ! [C_24,D_25,A_949] :
      ( r2_hidden(k4_tarski(C_24,D_25),k4_relat_1(u1_orders_2(A_949)))
      | ~ r2_hidden(k4_tarski(D_25,C_24),u1_orders_2('#skF_5'))
      | ~ v1_relat_1(k4_relat_1(u1_orders_2('#skF_5')))
      | ~ v1_relat_1(u1_orders_2('#skF_5'))
      | k7_lattice3(A_949) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_949) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40469,c_20])).

tff(c_40755,plain,(
    ! [C_24,D_25,A_949] :
      ( r2_hidden(k4_tarski(C_24,D_25),k4_relat_1(u1_orders_2(A_949)))
      | ~ r2_hidden(k4_tarski(D_25,C_24),u1_orders_2('#skF_5'))
      | k7_lattice3(A_949) != k7_lattice3('#skF_5')
      | ~ l1_orders_2(A_949) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39088,c_39367,c_40647])).

tff(c_39405,plain,(
    ! [B_30,C_32] :
      ( r1_orders_2(k7_lattice3('#skF_5'),B_30,C_32)
      | ~ r2_hidden(k4_tarski(B_30,C_32),k4_relat_1(u1_orders_2('#skF_5')))
      | ~ m1_subset_1(C_32,u1_struct_0(k7_lattice3('#skF_5')))
      | ~ m1_subset_1(B_30,u1_struct_0(k7_lattice3('#skF_5')))
      | ~ l1_orders_2(k7_lattice3('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39247,c_22])).

tff(c_57740,plain,(
    ! [B_1201,C_1202] :
      ( r1_orders_2(k7_lattice3('#skF_5'),B_1201,C_1202)
      | ~ r2_hidden(k4_tarski(B_1201,C_1202),k4_relat_1(u1_orders_2('#skF_5')))
      | ~ m1_subset_1(C_1202,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1201,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31169,c_32210,c_32210,c_39405])).

tff(c_57752,plain,(
    ! [C_24,D_25] :
      ( r1_orders_2(k7_lattice3('#skF_5'),C_24,D_25)
      | ~ m1_subset_1(D_25,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_24,u1_struct_0('#skF_5'))
      | ~ r2_hidden(k4_tarski(D_25,C_24),u1_orders_2('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40755,c_57740])).

tff(c_57951,plain,(
    ! [C_1203,D_1204] :
      ( r1_orders_2(k7_lattice3('#skF_5'),C_1203,D_1204)
      | ~ m1_subset_1(D_1204,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_1203,u1_struct_0('#skF_5'))
      | ~ r2_hidden(k4_tarski(D_1204,C_1203),u1_orders_2('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_57752])).

tff(c_58046,plain,(
    ! [C_32,B_30] :
      ( r1_orders_2(k7_lattice3('#skF_5'),C_32,B_30)
      | ~ r1_orders_2('#skF_5',B_30,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_30,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_57951])).

tff(c_58123,plain,(
    ! [C_1205,B_1206] :
      ( r1_orders_2(k7_lattice3('#skF_5'),C_1205,B_1206)
      | ~ r1_orders_2('#skF_5',B_1206,C_1205)
      | ~ m1_subset_1(C_1205,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_1206,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58046])).

tff(c_31071,plain,(
    ~ r1_orders_2(k7_lattice3('#skF_5'),k8_lattice3('#skF_5','#skF_7'),k8_lattice3('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_31107,plain,(
    ~ r1_orders_2(k7_lattice3('#skF_5'),'#skF_7',k8_lattice3('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31103,c_31071])).

tff(c_31116,plain,(
    ~ r1_orders_2(k7_lattice3('#skF_5'),'#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31106,c_31107])).

tff(c_58128,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_58123,c_31116])).

tff(c_58135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_31072,c_58128])).

%------------------------------------------------------------------------------
