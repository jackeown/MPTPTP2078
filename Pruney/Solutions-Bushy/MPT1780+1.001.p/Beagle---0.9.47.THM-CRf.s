%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1780+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:22 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 166 expanded)
%              Number of leaves         :   41 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  209 ( 444 expanded)
%              Number of equality atoms :   33 (  89 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k3_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k4_tmap_1,type,(
    k4_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_struct_0,type,(
    k3_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,u1_struct_0(B))
                 => k1_funct_1(k4_tmap_1(A,B),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k3_struct_0(A) = k6_partfun1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_struct_0)).

tff(f_97,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v1_funct_1(k3_struct_0(A))
        & v1_funct_2(k3_struct_0(A),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k3_struct_0(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_struct_0)).

tff(f_77,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => k4_tmap_1(A,B) = k2_tmap_1(A,A,k3_struct_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tmap_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_16,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_24,plain,(
    ! [A_29,B_30] :
      ( r2_hidden(A_29,B_30)
      | v1_xboole_0(B_30)
      | ~ m1_subset_1(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2,plain,(
    ! [A_1] :
      ( k6_partfun1(u1_struct_0(A_1)) = k3_struct_0(A_1)
      | ~ l1_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_22,plain,(
    ! [A_28] : k6_relat_1(A_28) = k6_partfun1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    ! [B_32,A_31] :
      ( k1_funct_1(k6_relat_1(B_32),A_31) = A_31
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_72,plain,(
    ! [B_47,A_48] :
      ( k1_funct_1(k6_partfun1(B_47),A_48) = A_48
      | ~ r2_hidden(A_48,B_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_96,plain,(
    ! [A_56,A_57] :
      ( k1_funct_1(k3_struct_0(A_56),A_57) = A_57
      | ~ r2_hidden(A_57,u1_struct_0(A_56))
      | ~ l1_struct_0(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_111,plain,(
    ! [A_58,A_59] :
      ( k1_funct_1(k3_struct_0(A_58),A_59) = A_59
      | ~ l1_struct_0(A_58)
      | v1_xboole_0(u1_struct_0(A_58))
      | ~ m1_subset_1(A_59,u1_struct_0(A_58)) ) ),
    inference(resolution,[status(thm)],[c_24,c_96])).

tff(c_115,plain,
    ( k1_funct_1(k3_struct_0('#skF_1'),'#skF_3') = '#skF_3'
    | ~ l1_struct_0('#skF_1')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_111])).

tff(c_120,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_123,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_120])).

tff(c_127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_123])).

tff(c_129,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_36,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_128,plain,
    ( v1_xboole_0(u1_struct_0('#skF_1'))
    | k1_funct_1(k3_struct_0('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_130,plain,(
    k1_funct_1(k3_struct_0('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_12,plain,(
    ! [A_20] :
      ( v1_funct_1(k3_struct_0(A_20))
      | ~ l1_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_59,plain,(
    ! [A_44] :
      ( k6_partfun1(u1_struct_0(A_44)) = k3_struct_0(A_44)
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_14,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_46,plain,(
    ! [A_21] : v1_relat_1(k6_partfun1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_14])).

tff(c_64,plain,(
    ! [A_44] :
      ( v1_relat_1(k3_struct_0(A_44))
      | ~ l1_struct_0(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_46])).

tff(c_32,plain,(
    r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6,plain,(
    ! [A_17,B_19] :
      ( k2_tmap_1(A_17,A_17,k3_struct_0(A_17),B_19) = k4_tmap_1(A_17,B_19)
      | ~ m1_pre_topc(B_19,A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_20] :
      ( v1_funct_2(k3_struct_0(A_20),u1_struct_0(A_20),u1_struct_0(A_20))
      | ~ l1_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_20] :
      ( m1_subset_1(k3_struct_0(A_20),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20),u1_struct_0(A_20))))
      | ~ l1_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_153,plain,(
    ! [A_68,B_69,C_70,D_71] :
      ( k2_partfun1(u1_struct_0(A_68),u1_struct_0(B_69),C_70,u1_struct_0(D_71)) = k2_tmap_1(A_68,B_69,C_70,D_71)
      | ~ m1_pre_topc(D_71,A_68)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68),u1_struct_0(B_69))))
      | ~ v1_funct_2(C_70,u1_struct_0(A_68),u1_struct_0(B_69))
      | ~ v1_funct_1(C_70)
      | ~ l1_pre_topc(B_69)
      | ~ v2_pre_topc(B_69)
      | v2_struct_0(B_69)
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_157,plain,(
    ! [A_72,D_73] :
      ( k2_partfun1(u1_struct_0(A_72),u1_struct_0(A_72),k3_struct_0(A_72),u1_struct_0(D_73)) = k2_tmap_1(A_72,A_72,k3_struct_0(A_72),D_73)
      | ~ m1_pre_topc(D_73,A_72)
      | ~ v1_funct_2(k3_struct_0(A_72),u1_struct_0(A_72),u1_struct_0(A_72))
      | ~ v1_funct_1(k3_struct_0(A_72))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72)
      | ~ l1_struct_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_8,c_153])).

tff(c_116,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( k2_partfun1(A_60,B_61,C_62,D_63) = k7_relat_1(C_62,D_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_funct_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_119,plain,(
    ! [A_20,D_63] :
      ( k2_partfun1(u1_struct_0(A_20),u1_struct_0(A_20),k3_struct_0(A_20),D_63) = k7_relat_1(k3_struct_0(A_20),D_63)
      | ~ v1_funct_1(k3_struct_0(A_20))
      | ~ l1_struct_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_8,c_116])).

tff(c_173,plain,(
    ! [A_74,D_75] :
      ( k7_relat_1(k3_struct_0(A_74),u1_struct_0(D_75)) = k2_tmap_1(A_74,A_74,k3_struct_0(A_74),D_75)
      | ~ v1_funct_1(k3_struct_0(A_74))
      | ~ l1_struct_0(A_74)
      | ~ m1_pre_topc(D_75,A_74)
      | ~ v1_funct_2(k3_struct_0(A_74),u1_struct_0(A_74),u1_struct_0(A_74))
      | ~ v1_funct_1(k3_struct_0(A_74))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74)
      | ~ l1_struct_0(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_119])).

tff(c_177,plain,(
    ! [A_76,D_77] :
      ( k7_relat_1(k3_struct_0(A_76),u1_struct_0(D_77)) = k2_tmap_1(A_76,A_76,k3_struct_0(A_76),D_77)
      | ~ m1_pre_topc(D_77,A_76)
      | ~ v1_funct_1(k3_struct_0(A_76))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76)
      | ~ l1_struct_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_10,c_173])).

tff(c_28,plain,(
    ! [C_35,B_34,A_33] :
      ( k1_funct_1(k7_relat_1(C_35,B_34),A_33) = k1_funct_1(C_35,A_33)
      | ~ r2_hidden(A_33,B_34)
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_221,plain,(
    ! [A_80,D_81,A_82] :
      ( k1_funct_1(k2_tmap_1(A_80,A_80,k3_struct_0(A_80),D_81),A_82) = k1_funct_1(k3_struct_0(A_80),A_82)
      | ~ r2_hidden(A_82,u1_struct_0(D_81))
      | ~ v1_funct_1(k3_struct_0(A_80))
      | ~ v1_relat_1(k3_struct_0(A_80))
      | ~ m1_pre_topc(D_81,A_80)
      | ~ v1_funct_1(k3_struct_0(A_80))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80)
      | ~ l1_struct_0(A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_28])).

tff(c_236,plain,(
    ! [A_83,B_84,A_85] :
      ( k1_funct_1(k4_tmap_1(A_83,B_84),A_85) = k1_funct_1(k3_struct_0(A_83),A_85)
      | ~ r2_hidden(A_85,u1_struct_0(B_84))
      | ~ v1_funct_1(k3_struct_0(A_83))
      | ~ v1_relat_1(k3_struct_0(A_83))
      | ~ m1_pre_topc(B_84,A_83)
      | ~ v1_funct_1(k3_struct_0(A_83))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83)
      | ~ l1_struct_0(A_83)
      | ~ m1_pre_topc(B_84,A_83)
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_221])).

tff(c_244,plain,(
    ! [A_86] :
      ( k1_funct_1(k4_tmap_1(A_86,'#skF_2'),'#skF_3') = k1_funct_1(k3_struct_0(A_86),'#skF_3')
      | ~ v1_relat_1(k3_struct_0(A_86))
      | ~ v1_funct_1(k3_struct_0(A_86))
      | ~ l1_struct_0(A_86)
      | ~ m1_pre_topc('#skF_2',A_86)
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_32,c_236])).

tff(c_249,plain,(
    ! [A_87] :
      ( k1_funct_1(k4_tmap_1(A_87,'#skF_2'),'#skF_3') = k1_funct_1(k3_struct_0(A_87),'#skF_3')
      | ~ v1_funct_1(k3_struct_0(A_87))
      | ~ m1_pre_topc('#skF_2',A_87)
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87)
      | ~ l1_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_64,c_244])).

tff(c_254,plain,(
    ! [A_88] :
      ( k1_funct_1(k4_tmap_1(A_88,'#skF_2'),'#skF_3') = k1_funct_1(k3_struct_0(A_88),'#skF_3')
      | ~ m1_pre_topc('#skF_2',A_88)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88)
      | ~ l1_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_12,c_249])).

tff(c_30,plain,(
    k1_funct_1(k4_tmap_1('#skF_1','#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_260,plain,
    ( k1_funct_1(k3_struct_0('#skF_1'),'#skF_3') != '#skF_3'
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_30])).

tff(c_266,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_42,c_40,c_36,c_130,c_260])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_266])).

tff(c_269,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_18,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(u1_struct_0(A_23))
      | ~ l1_struct_0(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_282,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_269,c_18])).

tff(c_285,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_282])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_285])).

%------------------------------------------------------------------------------
