%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:46 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 513 expanded)
%              Number of leaves         :   27 ( 182 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 (1203 expanded)
%              Number of equality atoms :   44 ( 344 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3401,plain,(
    ! [A_241] :
      ( r1_tarski(A_241,k2_zfmisc_1(k1_relat_1(A_241),k2_relat_1(A_241)))
      | ~ v1_relat_1(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [A_6] : v1_xboole_0('#skF_1'(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_63,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [A_6] : '#skF_1'(A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_63])).

tff(c_18,plain,(
    ! [A_6] : m1_subset_1('#skF_1'(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_97,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_18])).

tff(c_100,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_108,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_97,c_100])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_148,plain,(
    ! [A_38,B_39,C_40] :
      ( k1_relset_1(A_38,B_39,C_40) = k1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_224,plain,(
    ! [A_54,B_55,A_56] :
      ( k1_relset_1(A_54,B_55,A_56) = k1_relat_1(A_56)
      | ~ r1_tarski(A_56,k2_zfmisc_1(A_54,B_55)) ) ),
    inference(resolution,[status(thm)],[c_22,c_148])).

tff(c_242,plain,(
    ! [A_10] :
      ( k1_relset_1(k1_relat_1(A_10),k2_relat_1(A_10),A_10) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_24,c_224])).

tff(c_384,plain,(
    ! [B_67,C_68,A_69] :
      ( k1_xboole_0 = B_67
      | v1_funct_2(C_68,A_69,B_67)
      | k1_relset_1(A_69,B_67,C_68) != A_69
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1262,plain,(
    ! [B_130,A_131,A_132] :
      ( k1_xboole_0 = B_130
      | v1_funct_2(A_131,A_132,B_130)
      | k1_relset_1(A_132,B_130,A_131) != A_132
      | ~ r1_tarski(A_131,k2_zfmisc_1(A_132,B_130)) ) ),
    inference(resolution,[status(thm)],[c_22,c_384])).

tff(c_2876,plain,(
    ! [A_216] :
      ( k2_relat_1(A_216) = k1_xboole_0
      | v1_funct_2(A_216,k1_relat_1(A_216),k2_relat_1(A_216))
      | k1_relset_1(k1_relat_1(A_216),k2_relat_1(A_216),A_216) != k1_relat_1(A_216)
      | ~ v1_relat_1(A_216) ) ),
    inference(resolution,[status(thm)],[c_24,c_1262])).

tff(c_44,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_96,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_2883,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2876,c_96])).

tff(c_2895,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2883])).

tff(c_2898,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2895])).

tff(c_2901,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_2898])).

tff(c_2905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2901])).

tff(c_2906,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2895])).

tff(c_144,plain,(
    ! [A_37] :
      ( r1_tarski(A_37,k2_zfmisc_1(k1_relat_1(A_37),k2_relat_1(A_37)))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_147,plain,(
    ! [A_37] :
      ( k2_zfmisc_1(k1_relat_1(A_37),k2_relat_1(A_37)) = A_37
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_37),k2_relat_1(A_37)),A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_144,c_4])).

tff(c_2915,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'),k1_xboole_0),'#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2906,c_147])).

tff(c_2927,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_108,c_12,c_12,c_2906,c_2915])).

tff(c_164,plain,(
    ! [A_38,B_39] : k1_relset_1(A_38,B_39,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_97,c_148])).

tff(c_265,plain,(
    ! [A_58,B_59,C_60] :
      ( m1_subset_1(k1_relset_1(A_58,B_59,C_60),k1_zfmisc_1(A_58))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_284,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_38))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_265])).

tff(c_293,plain,(
    ! [A_61] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_61)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_284])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_311,plain,(
    ! [A_62] : r1_tarski(k1_relat_1(k1_xboole_0),A_62) ),
    inference(resolution,[status(thm)],[c_293,c_20])).

tff(c_110,plain,(
    ! [B_32,A_33] :
      ( B_32 = A_33
      | ~ r1_tarski(B_32,A_33)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_108,c_110])).

tff(c_331,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_311,c_115])).

tff(c_335,plain,(
    ! [A_38,B_39] : k1_relset_1(A_38,B_39,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_164])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_427,plain,(
    ! [C_72,B_73] :
      ( v1_funct_2(C_72,k1_xboole_0,B_73)
      | k1_relset_1(k1_xboole_0,B_73,C_72) != k1_xboole_0
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_34])).

tff(c_436,plain,(
    ! [B_73] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_73)
      | k1_relset_1(k1_xboole_0,B_73,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_97,c_427])).

tff(c_442,plain,(
    ! [B_73] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_436])).

tff(c_2967,plain,(
    ! [B_73] : v1_funct_2('#skF_2','#skF_2',B_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2927,c_2927,c_442])).

tff(c_2972,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2927,c_2927,c_331])).

tff(c_2908,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2906,c_96])).

tff(c_3084,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2927,c_2908])).

tff(c_3086,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2972,c_3084])).

tff(c_3347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2967,c_3086])).

tff(c_3348,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3400,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_22,c_3348])).

tff(c_3404,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3401,c_3400])).

tff(c_3410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3404])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.85  
% 4.63/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.85  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2
% 4.63/1.85  
% 4.63/1.85  %Foreground sorts:
% 4.63/1.85  
% 4.63/1.85  
% 4.63/1.85  %Background operators:
% 4.63/1.85  
% 4.63/1.85  
% 4.63/1.85  %Foreground operators:
% 4.63/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.63/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.85  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.63/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.63/1.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.63/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.63/1.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.63/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.63/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.63/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.63/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.63/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.85  
% 4.63/1.87  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.63/1.87  tff(f_54, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 4.63/1.87  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.63/1.87  tff(f_46, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 4.63/1.87  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.63/1.87  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.63/1.87  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.63/1.87  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.63/1.87  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.63/1.87  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.63/1.87  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.87  tff(c_3401, plain, (![A_241]: (r1_tarski(A_241, k2_zfmisc_1(k1_relat_1(A_241), k2_relat_1(A_241))) | ~v1_relat_1(A_241))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.63/1.87  tff(c_22, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.63/1.87  tff(c_16, plain, (![A_6]: (v1_xboole_0('#skF_1'(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.63/1.87  tff(c_63, plain, (![A_23]: (k1_xboole_0=A_23 | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.63/1.87  tff(c_67, plain, (![A_6]: ('#skF_1'(A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_63])).
% 4.63/1.87  tff(c_18, plain, (![A_6]: (m1_subset_1('#skF_1'(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.63/1.87  tff(c_97, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_18])).
% 4.63/1.87  tff(c_100, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.63/1.87  tff(c_108, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_97, c_100])).
% 4.63/1.87  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.63/1.87  tff(c_24, plain, (![A_10]: (r1_tarski(A_10, k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.63/1.87  tff(c_148, plain, (![A_38, B_39, C_40]: (k1_relset_1(A_38, B_39, C_40)=k1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.63/1.87  tff(c_224, plain, (![A_54, B_55, A_56]: (k1_relset_1(A_54, B_55, A_56)=k1_relat_1(A_56) | ~r1_tarski(A_56, k2_zfmisc_1(A_54, B_55)))), inference(resolution, [status(thm)], [c_22, c_148])).
% 4.63/1.87  tff(c_242, plain, (![A_10]: (k1_relset_1(k1_relat_1(A_10), k2_relat_1(A_10), A_10)=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_24, c_224])).
% 4.63/1.87  tff(c_384, plain, (![B_67, C_68, A_69]: (k1_xboole_0=B_67 | v1_funct_2(C_68, A_69, B_67) | k1_relset_1(A_69, B_67, C_68)!=A_69 | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_67))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.63/1.87  tff(c_1262, plain, (![B_130, A_131, A_132]: (k1_xboole_0=B_130 | v1_funct_2(A_131, A_132, B_130) | k1_relset_1(A_132, B_130, A_131)!=A_132 | ~r1_tarski(A_131, k2_zfmisc_1(A_132, B_130)))), inference(resolution, [status(thm)], [c_22, c_384])).
% 4.63/1.87  tff(c_2876, plain, (![A_216]: (k2_relat_1(A_216)=k1_xboole_0 | v1_funct_2(A_216, k1_relat_1(A_216), k2_relat_1(A_216)) | k1_relset_1(k1_relat_1(A_216), k2_relat_1(A_216), A_216)!=k1_relat_1(A_216) | ~v1_relat_1(A_216))), inference(resolution, [status(thm)], [c_24, c_1262])).
% 4.63/1.87  tff(c_44, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.87  tff(c_42, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.87  tff(c_48, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 4.63/1.87  tff(c_96, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_48])).
% 4.63/1.87  tff(c_2883, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2876, c_96])).
% 4.63/1.87  tff(c_2895, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2883])).
% 4.63/1.87  tff(c_2898, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_2895])).
% 4.63/1.87  tff(c_2901, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_242, c_2898])).
% 4.63/1.87  tff(c_2905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_2901])).
% 4.63/1.87  tff(c_2906, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2895])).
% 4.63/1.87  tff(c_144, plain, (![A_37]: (r1_tarski(A_37, k2_zfmisc_1(k1_relat_1(A_37), k2_relat_1(A_37))) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.63/1.87  tff(c_4, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.63/1.87  tff(c_147, plain, (![A_37]: (k2_zfmisc_1(k1_relat_1(A_37), k2_relat_1(A_37))=A_37 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_37), k2_relat_1(A_37)), A_37) | ~v1_relat_1(A_37))), inference(resolution, [status(thm)], [c_144, c_4])).
% 4.63/1.87  tff(c_2915, plain, (k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))='#skF_2' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'), k1_xboole_0), '#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2906, c_147])).
% 4.63/1.87  tff(c_2927, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_108, c_12, c_12, c_2906, c_2915])).
% 4.63/1.87  tff(c_164, plain, (![A_38, B_39]: (k1_relset_1(A_38, B_39, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_97, c_148])).
% 4.63/1.87  tff(c_265, plain, (![A_58, B_59, C_60]: (m1_subset_1(k1_relset_1(A_58, B_59, C_60), k1_zfmisc_1(A_58)) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.63/1.87  tff(c_284, plain, (![A_38, B_39]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_38)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(superposition, [status(thm), theory('equality')], [c_164, c_265])).
% 4.63/1.87  tff(c_293, plain, (![A_61]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_61)))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_284])).
% 4.63/1.87  tff(c_20, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.63/1.87  tff(c_311, plain, (![A_62]: (r1_tarski(k1_relat_1(k1_xboole_0), A_62))), inference(resolution, [status(thm)], [c_293, c_20])).
% 4.63/1.87  tff(c_110, plain, (![B_32, A_33]: (B_32=A_33 | ~r1_tarski(B_32, A_33) | ~r1_tarski(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.63/1.87  tff(c_115, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_108, c_110])).
% 4.63/1.87  tff(c_331, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_311, c_115])).
% 4.63/1.87  tff(c_335, plain, (![A_38, B_39]: (k1_relset_1(A_38, B_39, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_331, c_164])).
% 4.63/1.87  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.63/1.87  tff(c_34, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.63/1.87  tff(c_427, plain, (![C_72, B_73]: (v1_funct_2(C_72, k1_xboole_0, B_73) | k1_relset_1(k1_xboole_0, B_73, C_72)!=k1_xboole_0 | ~m1_subset_1(C_72, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_34])).
% 4.63/1.87  tff(c_436, plain, (![B_73]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_73) | k1_relset_1(k1_xboole_0, B_73, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_97, c_427])).
% 4.63/1.87  tff(c_442, plain, (![B_73]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_73))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_436])).
% 4.63/1.87  tff(c_2967, plain, (![B_73]: (v1_funct_2('#skF_2', '#skF_2', B_73))), inference(demodulation, [status(thm), theory('equality')], [c_2927, c_2927, c_442])).
% 4.63/1.87  tff(c_2972, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2927, c_2927, c_331])).
% 4.63/1.87  tff(c_2908, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2906, c_96])).
% 4.63/1.87  tff(c_3084, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2927, c_2908])).
% 4.63/1.87  tff(c_3086, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2972, c_3084])).
% 4.63/1.87  tff(c_3347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2967, c_3086])).
% 4.63/1.87  tff(c_3348, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_48])).
% 4.63/1.87  tff(c_3400, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_22, c_3348])).
% 4.63/1.87  tff(c_3404, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3401, c_3400])).
% 4.63/1.87  tff(c_3410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_3404])).
% 4.63/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.87  
% 4.63/1.87  Inference rules
% 4.63/1.87  ----------------------
% 4.63/1.87  #Ref     : 0
% 4.63/1.87  #Sup     : 712
% 4.63/1.87  #Fact    : 0
% 4.63/1.87  #Define  : 0
% 4.63/1.87  #Split   : 2
% 4.63/1.87  #Chain   : 0
% 4.63/1.87  #Close   : 0
% 4.63/1.87  
% 4.63/1.87  Ordering : KBO
% 4.63/1.87  
% 4.63/1.87  Simplification rules
% 4.63/1.87  ----------------------
% 4.63/1.87  #Subsume      : 86
% 4.63/1.87  #Demod        : 1546
% 4.63/1.87  #Tautology    : 343
% 4.63/1.87  #SimpNegUnit  : 0
% 4.63/1.87  #BackRed      : 63
% 4.63/1.87  
% 4.63/1.87  #Partial instantiations: 0
% 4.63/1.87  #Strategies tried      : 1
% 4.63/1.87  
% 4.63/1.87  Timing (in seconds)
% 4.63/1.87  ----------------------
% 4.63/1.87  Preprocessing        : 0.30
% 4.63/1.87  Parsing              : 0.15
% 4.63/1.87  CNF conversion       : 0.02
% 4.63/1.87  Main loop            : 0.79
% 4.63/1.87  Inferencing          : 0.26
% 4.63/1.87  Reduction            : 0.28
% 4.63/1.87  Demodulation         : 0.22
% 4.63/1.87  BG Simplification    : 0.04
% 4.63/1.87  Subsumption          : 0.15
% 4.63/1.87  Abstraction          : 0.05
% 4.63/1.87  MUC search           : 0.00
% 4.63/1.87  Cooper               : 0.00
% 4.63/1.87  Total                : 1.12
% 4.63/1.87  Index Insertion      : 0.00
% 4.63/1.87  Index Deletion       : 0.00
% 4.63/1.87  Index Matching       : 0.00
% 4.63/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
