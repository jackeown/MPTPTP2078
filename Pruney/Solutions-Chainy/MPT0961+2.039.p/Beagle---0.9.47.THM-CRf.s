%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:46 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 433 expanded)
%              Number of leaves         :   25 ( 155 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 (1072 expanded)
%              Number of equality atoms :   41 ( 305 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_79,axiom,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3020,plain,(
    ! [A_236] :
      ( r1_tarski(A_236,k2_zfmisc_1(k1_relat_1(A_236),k2_relat_1(A_236)))
      | ~ v1_relat_1(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_87,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_79])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,k2_zfmisc_1(k1_relat_1(A_11),k2_relat_1(A_11)))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_137,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_relset_1(A_45,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_210,plain,(
    ! [A_60,B_61,A_62] :
      ( k1_relset_1(A_60,B_61,A_62) = k1_relat_1(A_62)
      | ~ r1_tarski(A_62,k2_zfmisc_1(A_60,B_61)) ) ),
    inference(resolution,[status(thm)],[c_18,c_137])).

tff(c_228,plain,(
    ! [A_11] :
      ( k1_relset_1(k1_relat_1(A_11),k2_relat_1(A_11),A_11) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(resolution,[status(thm)],[c_22,c_210])).

tff(c_411,plain,(
    ! [B_76,C_77,A_78] :
      ( k1_xboole_0 = B_76
      | v1_funct_2(C_77,A_78,B_76)
      | k1_relset_1(A_78,B_76,C_77) != A_78
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1093,plain,(
    ! [B_138,A_139,A_140] :
      ( k1_xboole_0 = B_138
      | v1_funct_2(A_139,A_140,B_138)
      | k1_relset_1(A_140,B_138,A_139) != A_140
      | ~ r1_tarski(A_139,k2_zfmisc_1(A_140,B_138)) ) ),
    inference(resolution,[status(thm)],[c_18,c_411])).

tff(c_2597,plain,(
    ! [A_222] :
      ( k2_relat_1(A_222) = k1_xboole_0
      | v1_funct_2(A_222,k1_relat_1(A_222),k2_relat_1(A_222))
      | k1_relset_1(k1_relat_1(A_222),k2_relat_1(A_222),A_222) != k1_relat_1(A_222)
      | ~ v1_relat_1(A_222) ) ),
    inference(resolution,[status(thm)],[c_22,c_1093])).

tff(c_42,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_88,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_2604,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2597,c_88])).

tff(c_2616,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2604])).

tff(c_2619,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2616])).

tff(c_2622,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_2619])).

tff(c_2626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2622])).

tff(c_2627,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2616])).

tff(c_124,plain,(
    ! [A_36] :
      ( r1_tarski(A_36,k2_zfmisc_1(k1_relat_1(A_36),k2_relat_1(A_36)))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    ! [A_36] :
      ( k2_zfmisc_1(k1_relat_1(A_36),k2_relat_1(A_36)) = A_36
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_36),k2_relat_1(A_36)),A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(resolution,[status(thm)],[c_124,c_2])).

tff(c_2636,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) = '#skF_1'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0),'#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2627,c_127])).

tff(c_2648,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_87,c_10,c_10,c_2627,c_2636])).

tff(c_153,plain,(
    ! [A_45,B_46] : k1_relset_1(A_45,B_46,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_137])).

tff(c_268,plain,(
    ! [A_66,B_67,C_68] :
      ( m1_subset_1(k1_relset_1(A_66,B_67,C_68),k1_zfmisc_1(A_66))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_292,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_45))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_268])).

tff(c_302,plain,(
    ! [A_69] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_69)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_292])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_323,plain,(
    ! [A_70] : r1_tarski(k1_relat_1(k1_xboole_0),A_70) ),
    inference(resolution,[status(thm)],[c_302,c_16])).

tff(c_90,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_87,c_90])).

tff(c_343,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_323,c_95])).

tff(c_347,plain,(
    ! [A_45,B_46] : k1_relset_1(A_45,B_46,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_153])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [C_20,B_19] :
      ( v1_funct_2(C_20,k1_xboole_0,B_19)
      | k1_relset_1(k1_xboole_0,B_19,C_20) != k1_xboole_0
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_385,plain,(
    ! [C_73,B_74] :
      ( v1_funct_2(C_73,k1_xboole_0,B_74)
      | k1_relset_1(k1_xboole_0,B_74,C_73) != k1_xboole_0
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_32])).

tff(c_394,plain,(
    ! [B_74] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_74)
      | k1_relset_1(k1_xboole_0,B_74,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_385])).

tff(c_400,plain,(
    ! [B_74] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_394])).

tff(c_2687,plain,(
    ! [B_74] : v1_funct_2('#skF_1','#skF_1',B_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2648,c_2648,c_400])).

tff(c_2690,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2648,c_2648,c_343])).

tff(c_2629,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_88])).

tff(c_2805,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2690,c_2648,c_2629])).

tff(c_2978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2687,c_2805])).

tff(c_2979,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3008,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_18,c_2979])).

tff(c_3023,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3020,c_3008])).

tff(c_3029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3023])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:03:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.84  
% 4.56/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.84  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 4.56/1.84  
% 4.56/1.84  %Foreground sorts:
% 4.56/1.84  
% 4.56/1.84  
% 4.56/1.84  %Background operators:
% 4.56/1.84  
% 4.56/1.84  
% 4.56/1.84  %Foreground operators:
% 4.56/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.56/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.56/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.56/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.56/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.56/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.56/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.56/1.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.56/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.56/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.56/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.56/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.56/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.56/1.84  
% 4.66/1.85  tff(f_90, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 4.66/1.85  tff(f_53, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 4.66/1.85  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.66/1.85  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.66/1.85  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.66/1.85  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.66/1.85  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.66/1.85  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.66/1.85  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.66/1.85  tff(c_44, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.66/1.85  tff(c_3020, plain, (![A_236]: (r1_tarski(A_236, k2_zfmisc_1(k1_relat_1(A_236), k2_relat_1(A_236))) | ~v1_relat_1(A_236))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.66/1.85  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.66/1.85  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.66/1.85  tff(c_79, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~m1_subset_1(A_28, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.66/1.85  tff(c_87, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_79])).
% 4.66/1.85  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.66/1.85  tff(c_22, plain, (![A_11]: (r1_tarski(A_11, k2_zfmisc_1(k1_relat_1(A_11), k2_relat_1(A_11))) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.66/1.85  tff(c_137, plain, (![A_45, B_46, C_47]: (k1_relset_1(A_45, B_46, C_47)=k1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.66/1.85  tff(c_210, plain, (![A_60, B_61, A_62]: (k1_relset_1(A_60, B_61, A_62)=k1_relat_1(A_62) | ~r1_tarski(A_62, k2_zfmisc_1(A_60, B_61)))), inference(resolution, [status(thm)], [c_18, c_137])).
% 4.66/1.85  tff(c_228, plain, (![A_11]: (k1_relset_1(k1_relat_1(A_11), k2_relat_1(A_11), A_11)=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(resolution, [status(thm)], [c_22, c_210])).
% 4.66/1.85  tff(c_411, plain, (![B_76, C_77, A_78]: (k1_xboole_0=B_76 | v1_funct_2(C_77, A_78, B_76) | k1_relset_1(A_78, B_76, C_77)!=A_78 | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_76))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.66/1.85  tff(c_1093, plain, (![B_138, A_139, A_140]: (k1_xboole_0=B_138 | v1_funct_2(A_139, A_140, B_138) | k1_relset_1(A_140, B_138, A_139)!=A_140 | ~r1_tarski(A_139, k2_zfmisc_1(A_140, B_138)))), inference(resolution, [status(thm)], [c_18, c_411])).
% 4.66/1.85  tff(c_2597, plain, (![A_222]: (k2_relat_1(A_222)=k1_xboole_0 | v1_funct_2(A_222, k1_relat_1(A_222), k2_relat_1(A_222)) | k1_relset_1(k1_relat_1(A_222), k2_relat_1(A_222), A_222)!=k1_relat_1(A_222) | ~v1_relat_1(A_222))), inference(resolution, [status(thm)], [c_22, c_1093])).
% 4.66/1.85  tff(c_42, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.66/1.85  tff(c_40, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.66/1.85  tff(c_46, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 4.66/1.85  tff(c_88, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_46])).
% 4.66/1.85  tff(c_2604, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2597, c_88])).
% 4.66/1.85  tff(c_2616, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2604])).
% 4.66/1.85  tff(c_2619, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_2616])).
% 4.66/1.85  tff(c_2622, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_228, c_2619])).
% 4.66/1.85  tff(c_2626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_2622])).
% 4.66/1.85  tff(c_2627, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2616])).
% 4.66/1.85  tff(c_124, plain, (![A_36]: (r1_tarski(A_36, k2_zfmisc_1(k1_relat_1(A_36), k2_relat_1(A_36))) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.66/1.85  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/1.85  tff(c_127, plain, (![A_36]: (k2_zfmisc_1(k1_relat_1(A_36), k2_relat_1(A_36))=A_36 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_36), k2_relat_1(A_36)), A_36) | ~v1_relat_1(A_36))), inference(resolution, [status(thm)], [c_124, c_2])).
% 4.66/1.85  tff(c_2636, plain, (k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0), '#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2627, c_127])).
% 4.66/1.85  tff(c_2648, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_87, c_10, c_10, c_2627, c_2636])).
% 4.66/1.85  tff(c_153, plain, (![A_45, B_46]: (k1_relset_1(A_45, B_46, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_137])).
% 4.66/1.85  tff(c_268, plain, (![A_66, B_67, C_68]: (m1_subset_1(k1_relset_1(A_66, B_67, C_68), k1_zfmisc_1(A_66)) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.66/1.85  tff(c_292, plain, (![A_45, B_46]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_45)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(superposition, [status(thm), theory('equality')], [c_153, c_268])).
% 4.66/1.85  tff(c_302, plain, (![A_69]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_69)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_292])).
% 4.66/1.85  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.66/1.85  tff(c_323, plain, (![A_70]: (r1_tarski(k1_relat_1(k1_xboole_0), A_70))), inference(resolution, [status(thm)], [c_302, c_16])).
% 4.66/1.85  tff(c_90, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/1.85  tff(c_95, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_87, c_90])).
% 4.66/1.85  tff(c_343, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_323, c_95])).
% 4.66/1.85  tff(c_347, plain, (![A_45, B_46]: (k1_relset_1(A_45, B_46, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_343, c_153])).
% 4.66/1.85  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.66/1.85  tff(c_32, plain, (![C_20, B_19]: (v1_funct_2(C_20, k1_xboole_0, B_19) | k1_relset_1(k1_xboole_0, B_19, C_20)!=k1_xboole_0 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.66/1.85  tff(c_385, plain, (![C_73, B_74]: (v1_funct_2(C_73, k1_xboole_0, B_74) | k1_relset_1(k1_xboole_0, B_74, C_73)!=k1_xboole_0 | ~m1_subset_1(C_73, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_32])).
% 4.66/1.85  tff(c_394, plain, (![B_74]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_74) | k1_relset_1(k1_xboole_0, B_74, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_385])).
% 4.66/1.85  tff(c_400, plain, (![B_74]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_74))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_394])).
% 4.66/1.85  tff(c_2687, plain, (![B_74]: (v1_funct_2('#skF_1', '#skF_1', B_74))), inference(demodulation, [status(thm), theory('equality')], [c_2648, c_2648, c_400])).
% 4.66/1.85  tff(c_2690, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2648, c_2648, c_343])).
% 4.66/1.85  tff(c_2629, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2627, c_88])).
% 4.66/1.85  tff(c_2805, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2690, c_2648, c_2629])).
% 4.66/1.85  tff(c_2978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2687, c_2805])).
% 4.66/1.85  tff(c_2979, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_46])).
% 4.66/1.85  tff(c_3008, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_2979])).
% 4.66/1.85  tff(c_3023, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3020, c_3008])).
% 4.66/1.85  tff(c_3029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_3023])).
% 4.66/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.85  
% 4.66/1.85  Inference rules
% 4.66/1.85  ----------------------
% 4.66/1.85  #Ref     : 0
% 4.66/1.85  #Sup     : 635
% 4.66/1.85  #Fact    : 0
% 4.66/1.85  #Define  : 0
% 4.66/1.85  #Split   : 2
% 4.66/1.85  #Chain   : 0
% 4.66/1.85  #Close   : 0
% 4.66/1.85  
% 4.66/1.85  Ordering : KBO
% 4.66/1.85  
% 4.66/1.85  Simplification rules
% 4.66/1.85  ----------------------
% 4.66/1.85  #Subsume      : 88
% 4.66/1.85  #Demod        : 1390
% 4.66/1.85  #Tautology    : 302
% 4.66/1.85  #SimpNegUnit  : 0
% 4.66/1.85  #BackRed      : 56
% 4.66/1.85  
% 4.66/1.85  #Partial instantiations: 0
% 4.66/1.85  #Strategies tried      : 1
% 4.66/1.85  
% 4.66/1.85  Timing (in seconds)
% 4.66/1.85  ----------------------
% 4.66/1.86  Preprocessing        : 0.32
% 4.66/1.86  Parsing              : 0.17
% 4.66/1.86  CNF conversion       : 0.02
% 4.66/1.86  Main loop            : 0.76
% 4.66/1.86  Inferencing          : 0.25
% 4.66/1.86  Reduction            : 0.28
% 4.66/1.86  Demodulation         : 0.22
% 4.66/1.86  BG Simplification    : 0.03
% 4.66/1.86  Subsumption          : 0.14
% 4.66/1.86  Abstraction          : 0.05
% 4.66/1.86  MUC search           : 0.00
% 4.66/1.86  Cooper               : 0.00
% 4.66/1.86  Total                : 1.12
% 4.66/1.86  Index Insertion      : 0.00
% 4.66/1.86  Index Deletion       : 0.00
% 4.66/1.86  Index Matching       : 0.00
% 4.66/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
