%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:10 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 600 expanded)
%              Number of leaves         :   36 ( 218 expanded)
%              Depth                    :   12
%              Number of atoms          :  173 (1601 expanded)
%              Number of equality atoms :   57 ( 640 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_struct_0(B) = k1_xboole_0
                   => k2_struct_0(A) = k1_xboole_0 )
                 => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_struct_0(B)) = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_42,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_43,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_51,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_43])).

tff(c_40,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_43])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_50,c_34])).

tff(c_74,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_78,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_74])).

tff(c_10,plain,(
    ! [A_7] :
      ( k10_relat_1(A_7,k2_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [C_37,B_38,A_39] :
      ( v5_relat_1(C_37,B_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_39,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_88,plain,(
    v5_relat_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_84])).

tff(c_79,plain,(
    ! [B_35,A_36] :
      ( r1_tarski(k2_relat_1(B_35),A_36)
      | ~ v5_relat_1(B_35,A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_230,plain,(
    ! [B_67,A_68] :
      ( k3_xboole_0(k2_relat_1(B_67),A_68) = k2_relat_1(B_67)
      | ~ v5_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_79,c_2])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k10_relat_1(B_6,k3_xboole_0(k2_relat_1(B_6),A_5)) = k10_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_242,plain,(
    ! [B_69,A_70] :
      ( k10_relat_1(B_69,k2_relat_1(B_69)) = k10_relat_1(B_69,A_70)
      | ~ v1_relat_1(B_69)
      | ~ v5_relat_1(B_69,A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_8])).

tff(c_244,plain,
    ( k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k10_relat_1('#skF_3',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_242])).

tff(c_247,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k10_relat_1('#skF_3',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_244])).

tff(c_95,plain,(
    ! [C_42,A_43,B_44] :
      ( v4_relat_1(C_42,A_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_99,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_95])).

tff(c_110,plain,(
    ! [B_48,A_49] :
      ( k1_relat_1(B_48) = A_49
      | ~ v1_partfun1(B_48,A_49)
      | ~ v4_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_113,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_99,c_110])).

tff(c_116,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_113])).

tff(c_121,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_32,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_52,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_53,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36])).

tff(c_63,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_53])).

tff(c_161,plain,(
    ! [B_61,C_62,A_63] :
      ( k1_xboole_0 = B_61
      | v1_partfun1(C_62,A_63)
      | ~ v1_funct_2(C_62,A_63,B_61)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_61)))
      | ~ v1_funct_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_164,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_161])).

tff(c_167,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_63,c_164])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_52,c_167])).

tff(c_170,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_117,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( k8_relset_1(A_50,B_51,C_52,D_53) = k10_relat_1(C_52,D_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_120,plain,(
    ! [D_53] : k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_53) = k10_relat_1('#skF_3',D_53) ),
    inference(resolution,[status(thm)],[c_62,c_117])).

tff(c_217,plain,(
    ! [D_53] : k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',D_53) = k10_relat_1('#skF_3',D_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_120])).

tff(c_30,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_94,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_50,c_30])).

tff(c_173,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_170,c_94])).

tff(c_227,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_173])).

tff(c_248,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_227])).

tff(c_255,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_248])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_255])).

tff(c_260,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_276,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_51])).

tff(c_261,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_270,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_50])).

tff(c_293,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_270,c_34])).

tff(c_374,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k8_relset_1(A_100,B_101,C_102,D_103) = k10_relat_1(C_102,D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_377,plain,(
    ! [D_103] : k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',D_103) = k10_relat_1('#skF_3',D_103) ),
    inference(resolution,[status(thm)],[c_293,c_374])).

tff(c_318,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_270,c_261,c_260,c_30])).

tff(c_378,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_318])).

tff(c_12,plain,(
    ! [C_10,A_8,B_9] :
      ( v1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_297,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_293,c_12])).

tff(c_298,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_302,plain,(
    v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_293,c_298])).

tff(c_329,plain,(
    ! [B_90,A_91] :
      ( k1_relat_1(B_90) = A_91
      | ~ v1_partfun1(B_90,A_91)
      | ~ v4_relat_1(B_90,A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_332,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_partfun1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_302,c_329])).

tff(c_335,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_332])).

tff(c_336,plain,(
    ~ v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_271,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_36])).

tff(c_282,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_271])).

tff(c_353,plain,(
    ! [C_98,B_99] :
      ( v1_partfun1(C_98,k1_xboole_0)
      | ~ v1_funct_2(C_98,k1_xboole_0,B_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_99)))
      | ~ v1_funct_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_356,plain,
    ( v1_partfun1('#skF_3',k1_xboole_0)
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_293,c_353])).

tff(c_359,plain,(
    v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_282,c_356])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_359])).

tff(c_362,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_313,plain,(
    ! [C_84,B_85,A_86] :
      ( v5_relat_1(C_84,B_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_317,plain,(
    v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_293,c_313])).

tff(c_303,plain,(
    ! [B_80,A_81] :
      ( r1_tarski(k2_relat_1(B_80),A_81)
      | ~ v5_relat_1(B_80,A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_388,plain,(
    ! [B_105,A_106] :
      ( k3_xboole_0(k2_relat_1(B_105),A_106) = k2_relat_1(B_105)
      | ~ v5_relat_1(B_105,A_106)
      | ~ v1_relat_1(B_105) ) ),
    inference(resolution,[status(thm)],[c_303,c_2])).

tff(c_400,plain,(
    ! [B_107,A_108] :
      ( k10_relat_1(B_107,k2_relat_1(B_107)) = k10_relat_1(B_107,A_108)
      | ~ v1_relat_1(B_107)
      | ~ v5_relat_1(B_107,A_108)
      | ~ v1_relat_1(B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_8])).

tff(c_402,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_317,c_400])).

tff(c_405,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_402])).

tff(c_409,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_10])).

tff(c_416,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_362,c_409])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_378,c_416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.33  
% 2.54/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.34  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.54/1.34  
% 2.54/1.34  %Foreground sorts:
% 2.54/1.34  
% 2.54/1.34  
% 2.54/1.34  %Background operators:
% 2.54/1.34  
% 2.54/1.34  
% 2.54/1.34  %Foreground operators:
% 2.54/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.34  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.54/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.54/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.34  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.54/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.54/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.54/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.54/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.54/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.54/1.34  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.54/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.34  
% 2.54/1.36  tff(f_105, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 2.54/1.36  tff(f_86, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.54/1.36  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.54/1.36  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.54/1.36  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.54/1.36  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.54/1.36  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.54/1.36  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.54/1.36  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.54/1.36  tff(f_82, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 2.54/1.36  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.54/1.36  tff(c_42, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.54/1.36  tff(c_43, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.54/1.36  tff(c_51, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_43])).
% 2.54/1.36  tff(c_40, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.54/1.36  tff(c_50, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_43])).
% 2.54/1.36  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.54/1.36  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_50, c_34])).
% 2.54/1.36  tff(c_74, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.54/1.36  tff(c_78, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_74])).
% 2.54/1.36  tff(c_10, plain, (![A_7]: (k10_relat_1(A_7, k2_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.54/1.36  tff(c_84, plain, (![C_37, B_38, A_39]: (v5_relat_1(C_37, B_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_39, B_38))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.54/1.36  tff(c_88, plain, (v5_relat_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_62, c_84])).
% 2.54/1.36  tff(c_79, plain, (![B_35, A_36]: (r1_tarski(k2_relat_1(B_35), A_36) | ~v5_relat_1(B_35, A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.36  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.36  tff(c_230, plain, (![B_67, A_68]: (k3_xboole_0(k2_relat_1(B_67), A_68)=k2_relat_1(B_67) | ~v5_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_79, c_2])).
% 2.54/1.36  tff(c_8, plain, (![B_6, A_5]: (k10_relat_1(B_6, k3_xboole_0(k2_relat_1(B_6), A_5))=k10_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.54/1.36  tff(c_242, plain, (![B_69, A_70]: (k10_relat_1(B_69, k2_relat_1(B_69))=k10_relat_1(B_69, A_70) | ~v1_relat_1(B_69) | ~v5_relat_1(B_69, A_70) | ~v1_relat_1(B_69))), inference(superposition, [status(thm), theory('equality')], [c_230, c_8])).
% 2.54/1.36  tff(c_244, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k10_relat_1('#skF_3', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_242])).
% 2.54/1.36  tff(c_247, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k10_relat_1('#skF_3', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_244])).
% 2.54/1.36  tff(c_95, plain, (![C_42, A_43, B_44]: (v4_relat_1(C_42, A_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.54/1.36  tff(c_99, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_95])).
% 2.54/1.36  tff(c_110, plain, (![B_48, A_49]: (k1_relat_1(B_48)=A_49 | ~v1_partfun1(B_48, A_49) | ~v4_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.54/1.36  tff(c_113, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_99, c_110])).
% 2.54/1.36  tff(c_116, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_113])).
% 2.54/1.36  tff(c_121, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_116])).
% 2.54/1.36  tff(c_32, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.54/1.36  tff(c_52, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 2.54/1.36  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.54/1.36  tff(c_36, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.54/1.36  tff(c_53, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_36])).
% 2.54/1.36  tff(c_63, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_53])).
% 2.54/1.36  tff(c_161, plain, (![B_61, C_62, A_63]: (k1_xboole_0=B_61 | v1_partfun1(C_62, A_63) | ~v1_funct_2(C_62, A_63, B_61) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_61))) | ~v1_funct_1(C_62))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.54/1.36  tff(c_164, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_161])).
% 2.54/1.36  tff(c_167, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_63, c_164])).
% 2.54/1.36  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_52, c_167])).
% 2.54/1.36  tff(c_170, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_116])).
% 2.54/1.36  tff(c_117, plain, (![A_50, B_51, C_52, D_53]: (k8_relset_1(A_50, B_51, C_52, D_53)=k10_relat_1(C_52, D_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.54/1.36  tff(c_120, plain, (![D_53]: (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_53)=k10_relat_1('#skF_3', D_53))), inference(resolution, [status(thm)], [c_62, c_117])).
% 2.54/1.36  tff(c_217, plain, (![D_53]: (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', D_53)=k10_relat_1('#skF_3', D_53))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_120])).
% 2.54/1.36  tff(c_30, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.54/1.36  tff(c_94, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_50, c_30])).
% 2.54/1.36  tff(c_173, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_170, c_94])).
% 2.54/1.36  tff(c_227, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_173])).
% 2.54/1.36  tff(c_248, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_227])).
% 2.54/1.36  tff(c_255, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_248])).
% 2.54/1.36  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_255])).
% 2.54/1.36  tff(c_260, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.54/1.36  tff(c_276, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_260, c_51])).
% 2.54/1.36  tff(c_261, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.54/1.36  tff(c_270, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_261, c_50])).
% 2.54/1.36  tff(c_293, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_270, c_34])).
% 2.54/1.36  tff(c_374, plain, (![A_100, B_101, C_102, D_103]: (k8_relset_1(A_100, B_101, C_102, D_103)=k10_relat_1(C_102, D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.54/1.36  tff(c_377, plain, (![D_103]: (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', D_103)=k10_relat_1('#skF_3', D_103))), inference(resolution, [status(thm)], [c_293, c_374])).
% 2.54/1.36  tff(c_318, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_276, c_270, c_261, c_260, c_30])).
% 2.54/1.36  tff(c_378, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_377, c_318])).
% 2.54/1.36  tff(c_12, plain, (![C_10, A_8, B_9]: (v1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.54/1.36  tff(c_297, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_293, c_12])).
% 2.54/1.36  tff(c_298, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.54/1.36  tff(c_302, plain, (v4_relat_1('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_293, c_298])).
% 2.54/1.36  tff(c_329, plain, (![B_90, A_91]: (k1_relat_1(B_90)=A_91 | ~v1_partfun1(B_90, A_91) | ~v4_relat_1(B_90, A_91) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.54/1.36  tff(c_332, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_partfun1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_302, c_329])).
% 2.54/1.36  tff(c_335, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_partfun1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_297, c_332])).
% 2.54/1.36  tff(c_336, plain, (~v1_partfun1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_335])).
% 2.54/1.36  tff(c_271, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_270, c_36])).
% 2.54/1.36  tff(c_282, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_276, c_271])).
% 2.54/1.36  tff(c_353, plain, (![C_98, B_99]: (v1_partfun1(C_98, k1_xboole_0) | ~v1_funct_2(C_98, k1_xboole_0, B_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_99))) | ~v1_funct_1(C_98))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.54/1.36  tff(c_356, plain, (v1_partfun1('#skF_3', k1_xboole_0) | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_293, c_353])).
% 2.54/1.36  tff(c_359, plain, (v1_partfun1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_282, c_356])).
% 2.54/1.36  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_336, c_359])).
% 2.54/1.36  tff(c_362, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_335])).
% 2.54/1.36  tff(c_313, plain, (![C_84, B_85, A_86]: (v5_relat_1(C_84, B_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.54/1.36  tff(c_317, plain, (v5_relat_1('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_293, c_313])).
% 2.54/1.36  tff(c_303, plain, (![B_80, A_81]: (r1_tarski(k2_relat_1(B_80), A_81) | ~v5_relat_1(B_80, A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.36  tff(c_388, plain, (![B_105, A_106]: (k3_xboole_0(k2_relat_1(B_105), A_106)=k2_relat_1(B_105) | ~v5_relat_1(B_105, A_106) | ~v1_relat_1(B_105))), inference(resolution, [status(thm)], [c_303, c_2])).
% 2.54/1.36  tff(c_400, plain, (![B_107, A_108]: (k10_relat_1(B_107, k2_relat_1(B_107))=k10_relat_1(B_107, A_108) | ~v1_relat_1(B_107) | ~v5_relat_1(B_107, A_108) | ~v1_relat_1(B_107))), inference(superposition, [status(thm), theory('equality')], [c_388, c_8])).
% 2.54/1.36  tff(c_402, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_317, c_400])).
% 2.54/1.36  tff(c_405, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_297, c_402])).
% 2.54/1.36  tff(c_409, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_405, c_10])).
% 2.54/1.36  tff(c_416, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_297, c_362, c_409])).
% 2.54/1.36  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_378, c_416])).
% 2.54/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.36  
% 2.54/1.36  Inference rules
% 2.54/1.36  ----------------------
% 2.54/1.36  #Ref     : 0
% 2.54/1.36  #Sup     : 83
% 2.54/1.36  #Fact    : 0
% 2.54/1.36  #Define  : 0
% 2.54/1.36  #Split   : 3
% 2.54/1.36  #Chain   : 0
% 2.54/1.36  #Close   : 0
% 2.54/1.36  
% 2.54/1.36  Ordering : KBO
% 2.54/1.36  
% 2.54/1.36  Simplification rules
% 2.54/1.36  ----------------------
% 2.54/1.36  #Subsume      : 0
% 2.54/1.36  #Demod        : 54
% 2.54/1.36  #Tautology    : 54
% 2.54/1.36  #SimpNegUnit  : 3
% 2.54/1.36  #BackRed      : 11
% 2.54/1.36  
% 2.54/1.36  #Partial instantiations: 0
% 2.54/1.36  #Strategies tried      : 1
% 2.54/1.36  
% 2.54/1.36  Timing (in seconds)
% 2.54/1.36  ----------------------
% 2.54/1.36  Preprocessing        : 0.33
% 2.54/1.36  Parsing              : 0.17
% 2.54/1.36  CNF conversion       : 0.02
% 2.54/1.36  Main loop            : 0.25
% 2.54/1.36  Inferencing          : 0.10
% 2.54/1.36  Reduction            : 0.08
% 2.54/1.36  Demodulation         : 0.05
% 2.54/1.36  BG Simplification    : 0.02
% 2.54/1.36  Subsumption          : 0.03
% 2.54/1.36  Abstraction          : 0.01
% 2.54/1.36  MUC search           : 0.00
% 2.54/1.36  Cooper               : 0.00
% 2.54/1.36  Total                : 0.62
% 2.54/1.36  Index Insertion      : 0.00
% 2.54/1.36  Index Deletion       : 0.00
% 2.54/1.36  Index Matching       : 0.00
% 2.54/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
