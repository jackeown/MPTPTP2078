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
% DateTime   : Thu Dec  3 10:10:43 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 399 expanded)
%              Number of leaves         :   24 ( 142 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 (1052 expanded)
%              Number of equality atoms :   44 ( 339 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2113,plain,(
    ! [A_164] :
      ( r1_tarski(A_164,k2_zfmisc_1(k1_relat_1(A_164),k2_relat_1(A_164)))
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,k2_zfmisc_1(k1_relat_1(A_11),k2_relat_1(A_11)))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_334,plain,(
    ! [A_52,B_53,C_54] :
      ( k1_relset_1(A_52,B_53,C_54) = k1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_433,plain,(
    ! [A_68,B_69,A_70] :
      ( k1_relset_1(A_68,B_69,A_70) = k1_relat_1(A_70)
      | ~ r1_tarski(A_70,k2_zfmisc_1(A_68,B_69)) ) ),
    inference(resolution,[status(thm)],[c_18,c_334])).

tff(c_451,plain,(
    ! [A_11] :
      ( k1_relset_1(k1_relat_1(A_11),k2_relat_1(A_11),A_11) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(resolution,[status(thm)],[c_22,c_433])).

tff(c_362,plain,(
    ! [B_58,C_59,A_60] :
      ( k1_xboole_0 = B_58
      | v1_funct_2(C_59,A_60,B_58)
      | k1_relset_1(A_60,B_58,C_59) != A_60
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1119,plain,(
    ! [B_115,A_116,A_117] :
      ( k1_xboole_0 = B_115
      | v1_funct_2(A_116,A_117,B_115)
      | k1_relset_1(A_117,B_115,A_116) != A_117
      | ~ r1_tarski(A_116,k2_zfmisc_1(A_117,B_115)) ) ),
    inference(resolution,[status(thm)],[c_18,c_362])).

tff(c_1650,plain,(
    ! [A_149] :
      ( k2_relat_1(A_149) = k1_xboole_0
      | v1_funct_2(A_149,k1_relat_1(A_149),k2_relat_1(A_149))
      | k1_relset_1(k1_relat_1(A_149),k2_relat_1(A_149),A_149) != k1_relat_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(resolution,[status(thm)],[c_22,c_1119])).

tff(c_48,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_91,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_1657,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1650,c_91])).

tff(c_1681,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1657])).

tff(c_1686,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1681])).

tff(c_1689,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_1686])).

tff(c_1693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1689])).

tff(c_1694,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1681])).

tff(c_138,plain,(
    ! [A_37] :
      ( r1_tarski(A_37,k2_zfmisc_1(k1_relat_1(A_37),k2_relat_1(A_37)))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_150,plain,(
    ! [A_37] :
      ( k2_zfmisc_1(k1_relat_1(A_37),k2_relat_1(A_37)) = A_37
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_37),k2_relat_1(A_37)),A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_1730,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) = '#skF_1'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0),'#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1694,c_150])).

tff(c_1786,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8,c_12,c_12,c_1694,c_1730])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_18] :
      ( v1_funct_2(k1_xboole_0,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_18,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_55,plain,(
    ! [A_18] :
      ( v1_funct_2(k1_xboole_0,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_169,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_172,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_169])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_172])).

tff(c_178,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_346,plain,(
    ! [B_55,C_56] :
      ( k1_relset_1(k1_xboole_0,B_55,C_56) = k1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_334])).

tff(c_348,plain,(
    ! [B_55] : k1_relset_1(k1_xboole_0,B_55,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_178,c_346])).

tff(c_353,plain,(
    ! [B_55] : k1_relset_1(k1_xboole_0,B_55,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_348])).

tff(c_38,plain,(
    ! [C_20,B_19] :
      ( v1_funct_2(C_20,k1_xboole_0,B_19)
      | k1_relset_1(k1_xboole_0,B_19,C_20) != k1_xboole_0
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_455,plain,(
    ! [C_71,B_72] :
      ( v1_funct_2(C_71,k1_xboole_0,B_72)
      | k1_relset_1(k1_xboole_0,B_72,C_71) != k1_xboole_0
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38])).

tff(c_457,plain,(
    ! [B_72] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_72)
      | k1_relset_1(k1_xboole_0,B_72,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_178,c_455])).

tff(c_463,plain,(
    ! [B_72] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_457])).

tff(c_1844,plain,(
    ! [B_72] : v1_funct_2('#skF_1','#skF_1',B_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_1786,c_463])).

tff(c_1867,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_1786,c_30])).

tff(c_1696,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1694,c_91])).

tff(c_1810,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_1696])).

tff(c_2019,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1867,c_1810])).

tff(c_2047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1844,c_2019])).

tff(c_2048,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2058,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_18,c_2048])).

tff(c_2121,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2113,c_2058])).

tff(c_2133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.65  
% 3.91/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.65  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.91/1.65  
% 3.91/1.65  %Foreground sorts:
% 3.91/1.65  
% 3.91/1.65  
% 3.91/1.65  %Background operators:
% 3.91/1.65  
% 3.91/1.65  
% 3.91/1.65  %Foreground operators:
% 3.91/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.91/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.91/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.91/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.91/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.91/1.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.91/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.91/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.91/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.91/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.91/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.91/1.65  
% 3.91/1.66  tff(f_101, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.91/1.66  tff(f_54, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.91/1.66  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.91/1.66  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.91/1.66  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.91/1.66  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.91/1.66  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.91/1.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.91/1.66  tff(f_68, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.91/1.66  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.91/1.66  tff(c_2113, plain, (![A_164]: (r1_tarski(A_164, k2_zfmisc_1(k1_relat_1(A_164), k2_relat_1(A_164))) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.91/1.66  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.91/1.66  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.91/1.66  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.91/1.66  tff(c_22, plain, (![A_11]: (r1_tarski(A_11, k2_zfmisc_1(k1_relat_1(A_11), k2_relat_1(A_11))) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.91/1.66  tff(c_334, plain, (![A_52, B_53, C_54]: (k1_relset_1(A_52, B_53, C_54)=k1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.91/1.66  tff(c_433, plain, (![A_68, B_69, A_70]: (k1_relset_1(A_68, B_69, A_70)=k1_relat_1(A_70) | ~r1_tarski(A_70, k2_zfmisc_1(A_68, B_69)))), inference(resolution, [status(thm)], [c_18, c_334])).
% 3.91/1.66  tff(c_451, plain, (![A_11]: (k1_relset_1(k1_relat_1(A_11), k2_relat_1(A_11), A_11)=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(resolution, [status(thm)], [c_22, c_433])).
% 3.91/1.66  tff(c_362, plain, (![B_58, C_59, A_60]: (k1_xboole_0=B_58 | v1_funct_2(C_59, A_60, B_58) | k1_relset_1(A_60, B_58, C_59)!=A_60 | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_58))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.91/1.66  tff(c_1119, plain, (![B_115, A_116, A_117]: (k1_xboole_0=B_115 | v1_funct_2(A_116, A_117, B_115) | k1_relset_1(A_117, B_115, A_116)!=A_117 | ~r1_tarski(A_116, k2_zfmisc_1(A_117, B_115)))), inference(resolution, [status(thm)], [c_18, c_362])).
% 3.91/1.66  tff(c_1650, plain, (![A_149]: (k2_relat_1(A_149)=k1_xboole_0 | v1_funct_2(A_149, k1_relat_1(A_149), k2_relat_1(A_149)) | k1_relset_1(k1_relat_1(A_149), k2_relat_1(A_149), A_149)!=k1_relat_1(A_149) | ~v1_relat_1(A_149))), inference(resolution, [status(thm)], [c_22, c_1119])).
% 3.91/1.66  tff(c_48, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.91/1.66  tff(c_46, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.91/1.66  tff(c_52, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 3.91/1.66  tff(c_91, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.91/1.66  tff(c_1657, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1650, c_91])).
% 3.91/1.66  tff(c_1681, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1657])).
% 3.91/1.66  tff(c_1686, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1681])).
% 3.91/1.66  tff(c_1689, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_451, c_1686])).
% 3.91/1.66  tff(c_1693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1689])).
% 3.91/1.66  tff(c_1694, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1681])).
% 3.91/1.66  tff(c_138, plain, (![A_37]: (r1_tarski(A_37, k2_zfmisc_1(k1_relat_1(A_37), k2_relat_1(A_37))) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.91/1.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.66  tff(c_150, plain, (![A_37]: (k2_zfmisc_1(k1_relat_1(A_37), k2_relat_1(A_37))=A_37 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_37), k2_relat_1(A_37)), A_37) | ~v1_relat_1(A_37))), inference(resolution, [status(thm)], [c_138, c_2])).
% 3.91/1.66  tff(c_1730, plain, (k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0), '#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1694, c_150])).
% 3.91/1.66  tff(c_1786, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8, c_12, c_12, c_1694, c_1730])).
% 3.91/1.66  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.91/1.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.66  tff(c_34, plain, (![A_18]: (v1_funct_2(k1_xboole_0, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_18, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.91/1.66  tff(c_55, plain, (![A_18]: (v1_funct_2(k1_xboole_0, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 3.91/1.66  tff(c_169, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_55])).
% 3.91/1.66  tff(c_172, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_169])).
% 3.91/1.66  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_172])).
% 3.91/1.66  tff(c_178, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_55])).
% 3.91/1.66  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.91/1.66  tff(c_346, plain, (![B_55, C_56]: (k1_relset_1(k1_xboole_0, B_55, C_56)=k1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_334])).
% 3.91/1.66  tff(c_348, plain, (![B_55]: (k1_relset_1(k1_xboole_0, B_55, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_178, c_346])).
% 3.91/1.66  tff(c_353, plain, (![B_55]: (k1_relset_1(k1_xboole_0, B_55, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_348])).
% 3.91/1.66  tff(c_38, plain, (![C_20, B_19]: (v1_funct_2(C_20, k1_xboole_0, B_19) | k1_relset_1(k1_xboole_0, B_19, C_20)!=k1_xboole_0 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.91/1.66  tff(c_455, plain, (![C_71, B_72]: (v1_funct_2(C_71, k1_xboole_0, B_72) | k1_relset_1(k1_xboole_0, B_72, C_71)!=k1_xboole_0 | ~m1_subset_1(C_71, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38])).
% 3.91/1.66  tff(c_457, plain, (![B_72]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_72) | k1_relset_1(k1_xboole_0, B_72, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_178, c_455])).
% 3.91/1.66  tff(c_463, plain, (![B_72]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_457])).
% 3.91/1.66  tff(c_1844, plain, (![B_72]: (v1_funct_2('#skF_1', '#skF_1', B_72))), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_1786, c_463])).
% 3.91/1.66  tff(c_1867, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_1786, c_30])).
% 3.91/1.66  tff(c_1696, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1694, c_91])).
% 3.91/1.66  tff(c_1810, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_1696])).
% 3.91/1.66  tff(c_2019, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1867, c_1810])).
% 3.91/1.66  tff(c_2047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1844, c_2019])).
% 3.91/1.66  tff(c_2048, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_52])).
% 3.91/1.66  tff(c_2058, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_2048])).
% 3.91/1.66  tff(c_2121, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2113, c_2058])).
% 3.91/1.66  tff(c_2133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_2121])).
% 3.91/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.66  
% 3.91/1.66  Inference rules
% 3.91/1.66  ----------------------
% 3.91/1.66  #Ref     : 0
% 3.91/1.66  #Sup     : 439
% 3.91/1.66  #Fact    : 0
% 3.91/1.66  #Define  : 0
% 3.91/1.66  #Split   : 5
% 3.91/1.66  #Chain   : 0
% 3.91/1.66  #Close   : 0
% 3.91/1.66  
% 3.91/1.66  Ordering : KBO
% 3.91/1.66  
% 3.91/1.66  Simplification rules
% 3.91/1.66  ----------------------
% 3.91/1.66  #Subsume      : 89
% 3.91/1.66  #Demod        : 686
% 3.91/1.66  #Tautology    : 220
% 3.91/1.67  #SimpNegUnit  : 6
% 3.91/1.67  #BackRed      : 63
% 3.91/1.67  
% 3.91/1.67  #Partial instantiations: 0
% 3.91/1.67  #Strategies tried      : 1
% 3.91/1.67  
% 3.91/1.67  Timing (in seconds)
% 3.91/1.67  ----------------------
% 3.91/1.67  Preprocessing        : 0.31
% 3.91/1.67  Parsing              : 0.16
% 3.91/1.67  CNF conversion       : 0.02
% 3.91/1.67  Main loop            : 0.59
% 3.91/1.67  Inferencing          : 0.19
% 3.91/1.67  Reduction            : 0.19
% 3.91/1.67  Demodulation         : 0.14
% 3.91/1.67  BG Simplification    : 0.03
% 3.91/1.67  Subsumption          : 0.14
% 3.91/1.67  Abstraction          : 0.03
% 3.91/1.67  MUC search           : 0.00
% 3.91/1.67  Cooper               : 0.00
% 3.91/1.67  Total                : 0.93
% 3.91/1.67  Index Insertion      : 0.00
% 3.91/1.67  Index Deletion       : 0.00
% 3.91/1.67  Index Matching       : 0.00
% 3.91/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
