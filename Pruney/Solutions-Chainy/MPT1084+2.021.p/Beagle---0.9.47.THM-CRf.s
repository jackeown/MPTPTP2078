%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:22 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 386 expanded)
%              Number of leaves         :   33 ( 149 expanded)
%              Depth                    :   14
%              Number of atoms          :  151 (1188 expanded)
%              Number of equality atoms :   47 ( 387 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ! [C] :
                  ( m1_subset_1(C,A)
                 => k3_funct_2(A,A,B,C) = C )
             => r2_funct_2(A,A,B,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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

tff(f_98,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_14,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_88,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_95,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_99,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_95])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_108,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_117,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_108])).

tff(c_174,plain,(
    ! [B_77,A_78,C_79] :
      ( k1_xboole_0 = B_77
      | k1_relset_1(A_78,B_77,C_79) = A_78
      | ~ v1_funct_2(C_79,A_78,B_77)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_181,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_174])).

tff(c_185,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_117,c_181])).

tff(c_186,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_40,plain,(
    ! [A_23] : k6_relat_1(A_23) = k6_partfun1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_18,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_9),B_9),k1_relat_1(B_9))
      | k6_relat_1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_59,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_9),B_9),k1_relat_1(B_9))
      | k6_partfun1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18])).

tff(c_191,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_59])).

tff(c_198,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_54,c_186,c_186,c_191])).

tff(c_206,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_46,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_207,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_46])).

tff(c_236,plain,(
    ! [A_82,B_83,D_84] :
      ( r2_funct_2(A_82,B_83,D_84,D_84)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_2(D_84,A_82,B_83)
      | ~ v1_funct_1(D_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_241,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_236])).

tff(c_245,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_241])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_245])).

tff(c_249,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_16,plain,(
    ! [B_9] :
      ( k1_funct_1(B_9,'#skF_1'(k1_relat_1(B_9),B_9)) != '#skF_1'(k1_relat_1(B_9),B_9)
      | k6_relat_1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_280,plain,(
    ! [B_88] :
      ( k1_funct_1(B_88,'#skF_1'(k1_relat_1(B_88),B_88)) != '#skF_1'(k1_relat_1(B_88),B_88)
      | k6_partfun1(k1_relat_1(B_88)) = B_88
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16])).

tff(c_283,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_280])).

tff(c_285,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_54,c_186,c_186,c_283])).

tff(c_286,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_285])).

tff(c_248,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( m1_subset_1(B_2,A_1)
      | ~ r2_hidden(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_252,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_248,c_4])).

tff(c_255,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_252])).

tff(c_48,plain,(
    ! [C_32] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_32) = C_32
      | ~ m1_subset_1(C_32,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_262,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_255,c_48])).

tff(c_287,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k3_funct_2(A_89,B_90,C_91,D_92) = k1_funct_1(C_91,D_92)
      | ~ m1_subset_1(D_92,A_89)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ v1_funct_2(C_91,A_89,B_90)
      | ~ v1_funct_1(C_91)
      | v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_289,plain,(
    ! [B_90,C_91] :
      ( k3_funct_2('#skF_2',B_90,C_91,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_91,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_90)))
      | ~ v1_funct_2(C_91,'#skF_2',B_90)
      | ~ v1_funct_1(C_91)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_255,c_287])).

tff(c_327,plain,(
    ! [B_100,C_101] :
      ( k3_funct_2('#skF_2',B_100,C_101,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_101,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_100)))
      | ~ v1_funct_2(C_101,'#skF_2',B_100)
      | ~ v1_funct_1(C_101) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_289])).

tff(c_334,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_327])).

tff(c_338,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_262,c_334])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_286,c_338])).

tff(c_341,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_354,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_2])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.40  
% 2.63/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.40  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.63/1.40  
% 2.63/1.40  %Foreground sorts:
% 2.63/1.40  
% 2.63/1.40  
% 2.63/1.40  %Background operators:
% 2.63/1.40  
% 2.63/1.40  
% 2.63/1.40  %Foreground operators:
% 2.63/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.63/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.63/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.63/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.63/1.40  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.63/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.63/1.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.63/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.63/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.40  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.63/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.63/1.40  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.63/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.40  
% 2.63/1.42  tff(f_132, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 2.63/1.42  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.63/1.42  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.63/1.42  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.63/1.42  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.63/1.42  tff(f_98, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.63/1.42  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.63/1.42  tff(f_114, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.63/1.42  tff(f_39, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.63/1.42  tff(f_96, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.63/1.42  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.63/1.42  tff(c_56, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.63/1.42  tff(c_14, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.63/1.42  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.63/1.42  tff(c_88, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.63/1.42  tff(c_95, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_88])).
% 2.63/1.42  tff(c_99, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_95])).
% 2.63/1.42  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.63/1.42  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.63/1.42  tff(c_108, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.42  tff(c_117, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_108])).
% 2.63/1.42  tff(c_174, plain, (![B_77, A_78, C_79]: (k1_xboole_0=B_77 | k1_relset_1(A_78, B_77, C_79)=A_78 | ~v1_funct_2(C_79, A_78, B_77) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.63/1.42  tff(c_181, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_174])).
% 2.63/1.42  tff(c_185, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_117, c_181])).
% 2.63/1.42  tff(c_186, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitLeft, [status(thm)], [c_185])).
% 2.63/1.42  tff(c_40, plain, (![A_23]: (k6_relat_1(A_23)=k6_partfun1(A_23))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.63/1.42  tff(c_18, plain, (![B_9]: (r2_hidden('#skF_1'(k1_relat_1(B_9), B_9), k1_relat_1(B_9)) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.63/1.42  tff(c_59, plain, (![B_9]: (r2_hidden('#skF_1'(k1_relat_1(B_9), B_9), k1_relat_1(B_9)) | k6_partfun1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18])).
% 2.63/1.42  tff(c_191, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_186, c_59])).
% 2.63/1.42  tff(c_198, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_54, c_186, c_186, c_191])).
% 2.63/1.42  tff(c_206, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_198])).
% 2.63/1.42  tff(c_46, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.63/1.42  tff(c_207, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_46])).
% 2.63/1.42  tff(c_236, plain, (![A_82, B_83, D_84]: (r2_funct_2(A_82, B_83, D_84, D_84) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_2(D_84, A_82, B_83) | ~v1_funct_1(D_84))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.63/1.42  tff(c_241, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_236])).
% 2.63/1.42  tff(c_245, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_241])).
% 2.63/1.42  tff(c_247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_245])).
% 2.63/1.42  tff(c_249, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_198])).
% 2.63/1.42  tff(c_16, plain, (![B_9]: (k1_funct_1(B_9, '#skF_1'(k1_relat_1(B_9), B_9))!='#skF_1'(k1_relat_1(B_9), B_9) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.63/1.42  tff(c_280, plain, (![B_88]: (k1_funct_1(B_88, '#skF_1'(k1_relat_1(B_88), B_88))!='#skF_1'(k1_relat_1(B_88), B_88) | k6_partfun1(k1_relat_1(B_88))=B_88 | ~v1_funct_1(B_88) | ~v1_relat_1(B_88))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16])).
% 2.63/1.42  tff(c_283, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_186, c_280])).
% 2.63/1.42  tff(c_285, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_54, c_186, c_186, c_283])).
% 2.63/1.42  tff(c_286, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_249, c_285])).
% 2.63/1.42  tff(c_248, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_198])).
% 2.63/1.42  tff(c_4, plain, (![B_2, A_1]: (m1_subset_1(B_2, A_1) | ~r2_hidden(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.63/1.42  tff(c_252, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_248, c_4])).
% 2.63/1.42  tff(c_255, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_252])).
% 2.63/1.42  tff(c_48, plain, (![C_32]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_32)=C_32 | ~m1_subset_1(C_32, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.63/1.42  tff(c_262, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_255, c_48])).
% 2.63/1.42  tff(c_287, plain, (![A_89, B_90, C_91, D_92]: (k3_funct_2(A_89, B_90, C_91, D_92)=k1_funct_1(C_91, D_92) | ~m1_subset_1(D_92, A_89) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~v1_funct_2(C_91, A_89, B_90) | ~v1_funct_1(C_91) | v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.63/1.42  tff(c_289, plain, (![B_90, C_91]: (k3_funct_2('#skF_2', B_90, C_91, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_91, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_90))) | ~v1_funct_2(C_91, '#skF_2', B_90) | ~v1_funct_1(C_91) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_255, c_287])).
% 2.63/1.42  tff(c_327, plain, (![B_100, C_101]: (k3_funct_2('#skF_2', B_100, C_101, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_101, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_100))) | ~v1_funct_2(C_101, '#skF_2', B_100) | ~v1_funct_1(C_101))), inference(negUnitSimplification, [status(thm)], [c_56, c_289])).
% 2.63/1.42  tff(c_334, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_327])).
% 2.63/1.42  tff(c_338, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_262, c_334])).
% 2.63/1.42  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_286, c_338])).
% 2.63/1.42  tff(c_341, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_185])).
% 2.63/1.42  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.63/1.42  tff(c_354, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_341, c_2])).
% 2.63/1.42  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_354])).
% 2.63/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.42  
% 2.63/1.42  Inference rules
% 2.63/1.42  ----------------------
% 2.63/1.42  #Ref     : 0
% 2.63/1.42  #Sup     : 54
% 2.63/1.42  #Fact    : 0
% 2.63/1.42  #Define  : 0
% 2.63/1.42  #Split   : 4
% 2.63/1.42  #Chain   : 0
% 2.63/1.42  #Close   : 0
% 2.63/1.42  
% 2.63/1.42  Ordering : KBO
% 2.63/1.42  
% 2.63/1.42  Simplification rules
% 2.63/1.42  ----------------------
% 2.63/1.42  #Subsume      : 4
% 2.63/1.42  #Demod        : 97
% 2.63/1.42  #Tautology    : 22
% 2.63/1.42  #SimpNegUnit  : 11
% 2.63/1.42  #BackRed      : 14
% 2.63/1.42  
% 2.63/1.42  #Partial instantiations: 0
% 2.63/1.42  #Strategies tried      : 1
% 2.63/1.42  
% 2.63/1.42  Timing (in seconds)
% 2.63/1.42  ----------------------
% 2.63/1.42  Preprocessing        : 0.34
% 2.63/1.42  Parsing              : 0.18
% 2.63/1.42  CNF conversion       : 0.02
% 2.63/1.42  Main loop            : 0.24
% 2.63/1.42  Inferencing          : 0.08
% 2.63/1.42  Reduction            : 0.08
% 2.63/1.42  Demodulation         : 0.05
% 2.63/1.42  BG Simplification    : 0.02
% 2.63/1.42  Subsumption          : 0.05
% 2.63/1.42  Abstraction          : 0.01
% 2.63/1.42  MUC search           : 0.00
% 2.63/1.42  Cooper               : 0.00
% 2.63/1.42  Total                : 0.62
% 2.63/1.42  Index Insertion      : 0.00
% 2.63/1.42  Index Deletion       : 0.00
% 2.63/1.42  Index Matching       : 0.00
% 2.63/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
