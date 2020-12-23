%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:22 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 380 expanded)
%              Number of leaves         :   33 ( 147 expanded)
%              Depth                    :   13
%              Number of atoms          :  144 (1158 expanded)
%              Number of equality atoms :   47 ( 385 expanded)
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

tff(f_123,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_39,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_74,axiom,(
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

tff(f_89,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_67,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_67])).

tff(c_73,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_70])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_46,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_75,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_relset_1(A_42,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_79,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_75])).

tff(c_95,plain,(
    ! [B_56,A_57,C_58] :
      ( k1_xboole_0 = B_56
      | k1_relset_1(A_57,B_56,C_58) = A_57
      | ~ v1_funct_2(C_58,A_57,B_56)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_98,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_95])).

tff(c_101,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_98])).

tff(c_102,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_34,plain,(
    ! [A_23] : k6_relat_1(A_23) = k6_partfun1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_9),B_9),k1_relat_1(B_9))
      | k6_relat_1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_53,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_9),B_9),k1_relat_1(B_9))
      | k6_partfun1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12])).

tff(c_113,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),k1_relat_1('#skF_3'))
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_53])).

tff(c_124,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_48,c_102,c_102,c_113])).

tff(c_138,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_40,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_139,plain,(
    ~ r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_40])).

tff(c_157,plain,(
    ! [A_63,B_64,D_65] :
      ( r2_funct_2(A_63,B_64,D_65,D_65)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | ~ v1_funct_2(D_65,A_63,B_64)
      | ~ v1_funct_1(D_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_159,plain,
    ( r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_157])).

tff(c_162,plain,(
    r2_funct_2('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_159])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_162])).

tff(c_166,plain,(
    k6_partfun1('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_10,plain,(
    ! [B_9] :
      ( k1_funct_1(B_9,'#skF_1'(k1_relat_1(B_9),B_9)) != '#skF_1'(k1_relat_1(B_9),B_9)
      | k6_relat_1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_191,plain,(
    ! [B_69] :
      ( k1_funct_1(B_69,'#skF_1'(k1_relat_1(B_69),B_69)) != '#skF_1'(k1_relat_1(B_69),B_69)
      | k6_partfun1(k1_relat_1(B_69)) = B_69
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10])).

tff(c_194,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'(k1_relat_1('#skF_3'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_191])).

tff(c_196,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3')
    | k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_48,c_102,c_102,c_194])).

tff(c_197,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) != '#skF_1'('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_196])).

tff(c_165,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_176,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_165,c_4])).

tff(c_42,plain,(
    ! [C_32] :
      ( k3_funct_2('#skF_2','#skF_2','#skF_3',C_32) = C_32
      | ~ m1_subset_1(C_32,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_182,plain,(
    k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_42])).

tff(c_198,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( k3_funct_2(A_70,B_71,C_72,D_73) = k1_funct_1(C_72,D_73)
      | ~ m1_subset_1(D_73,A_70)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_2(C_72,A_70,B_71)
      | ~ v1_funct_1(C_72)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_200,plain,(
    ! [B_71,C_72] :
      ( k3_funct_2('#skF_2',B_71,C_72,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_72,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_71)))
      | ~ v1_funct_2(C_72,'#skF_2',B_71)
      | ~ v1_funct_1(C_72)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_176,c_198])).

tff(c_210,plain,(
    ! [B_74,C_75] :
      ( k3_funct_2('#skF_2',B_74,C_75,'#skF_1'('#skF_2','#skF_3')) = k1_funct_1(C_75,'#skF_1'('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_74)))
      | ~ v1_funct_2(C_75,'#skF_2',B_74)
      | ~ v1_funct_1(C_75) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_200])).

tff(c_213,plain,
    ( k3_funct_2('#skF_2','#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3')) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_210])).

tff(c_216,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3')) = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_182,c_213])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_216])).

tff(c_219,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_226,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_2])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:09:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.26  
% 2.24/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.26  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.24/1.26  
% 2.24/1.26  %Foreground sorts:
% 2.24/1.26  
% 2.24/1.26  
% 2.24/1.26  %Background operators:
% 2.24/1.26  
% 2.24/1.26  
% 2.24/1.26  %Foreground operators:
% 2.24/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.24/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.24/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.24/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.24/1.26  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.24/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.24/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.26  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.24/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.26  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.24/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.26  
% 2.24/1.28  tff(f_123, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t201_funct_2)).
% 2.24/1.28  tff(f_39, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.24/1.28  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.24/1.28  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.24/1.28  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.24/1.28  tff(f_89, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.24/1.28  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.24/1.28  tff(f_105, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.24/1.28  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.24/1.28  tff(f_87, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.24/1.28  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.24/1.28  tff(c_50, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.24/1.28  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.28  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.24/1.28  tff(c_67, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.24/1.28  tff(c_70, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_67])).
% 2.24/1.28  tff(c_73, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_70])).
% 2.24/1.28  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.24/1.28  tff(c_46, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.24/1.28  tff(c_75, plain, (![A_42, B_43, C_44]: (k1_relset_1(A_42, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.24/1.28  tff(c_79, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_75])).
% 2.24/1.28  tff(c_95, plain, (![B_56, A_57, C_58]: (k1_xboole_0=B_56 | k1_relset_1(A_57, B_56, C_58)=A_57 | ~v1_funct_2(C_58, A_57, B_56) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.24/1.28  tff(c_98, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_95])).
% 2.24/1.28  tff(c_101, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_98])).
% 2.24/1.28  tff(c_102, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitLeft, [status(thm)], [c_101])).
% 2.24/1.28  tff(c_34, plain, (![A_23]: (k6_relat_1(A_23)=k6_partfun1(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.24/1.28  tff(c_12, plain, (![B_9]: (r2_hidden('#skF_1'(k1_relat_1(B_9), B_9), k1_relat_1(B_9)) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.24/1.28  tff(c_53, plain, (![B_9]: (r2_hidden('#skF_1'(k1_relat_1(B_9), B_9), k1_relat_1(B_9)) | k6_partfun1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12])).
% 2.24/1.28  tff(c_113, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), k1_relat_1('#skF_3')) | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_102, c_53])).
% 2.24/1.28  tff(c_124, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_48, c_102, c_102, c_113])).
% 2.24/1.28  tff(c_138, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_124])).
% 2.24/1.28  tff(c_40, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.24/1.28  tff(c_139, plain, (~r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_40])).
% 2.24/1.28  tff(c_157, plain, (![A_63, B_64, D_65]: (r2_funct_2(A_63, B_64, D_65, D_65) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))) | ~v1_funct_2(D_65, A_63, B_64) | ~v1_funct_1(D_65))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.24/1.28  tff(c_159, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_157])).
% 2.24/1.28  tff(c_162, plain, (r2_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_159])).
% 2.24/1.28  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_162])).
% 2.24/1.28  tff(c_166, plain, (k6_partfun1('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_124])).
% 2.24/1.28  tff(c_10, plain, (![B_9]: (k1_funct_1(B_9, '#skF_1'(k1_relat_1(B_9), B_9))!='#skF_1'(k1_relat_1(B_9), B_9) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.24/1.28  tff(c_191, plain, (![B_69]: (k1_funct_1(B_69, '#skF_1'(k1_relat_1(B_69), B_69))!='#skF_1'(k1_relat_1(B_69), B_69) | k6_partfun1(k1_relat_1(B_69))=B_69 | ~v1_funct_1(B_69) | ~v1_relat_1(B_69))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10])).
% 2.24/1.28  tff(c_194, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'(k1_relat_1('#skF_3'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_102, c_191])).
% 2.24/1.28  tff(c_196, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3') | k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_48, c_102, c_102, c_194])).
% 2.24/1.28  tff(c_197, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))!='#skF_1'('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_166, c_196])).
% 2.24/1.28  tff(c_165, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_124])).
% 2.24/1.28  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.24/1.28  tff(c_176, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_165, c_4])).
% 2.24/1.28  tff(c_42, plain, (![C_32]: (k3_funct_2('#skF_2', '#skF_2', '#skF_3', C_32)=C_32 | ~m1_subset_1(C_32, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.24/1.28  tff(c_182, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_176, c_42])).
% 2.24/1.28  tff(c_198, plain, (![A_70, B_71, C_72, D_73]: (k3_funct_2(A_70, B_71, C_72, D_73)=k1_funct_1(C_72, D_73) | ~m1_subset_1(D_73, A_70) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_2(C_72, A_70, B_71) | ~v1_funct_1(C_72) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.24/1.28  tff(c_200, plain, (![B_71, C_72]: (k3_funct_2('#skF_2', B_71, C_72, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_72, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_71))) | ~v1_funct_2(C_72, '#skF_2', B_71) | ~v1_funct_1(C_72) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_176, c_198])).
% 2.24/1.28  tff(c_210, plain, (![B_74, C_75]: (k3_funct_2('#skF_2', B_74, C_75, '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1(C_75, '#skF_1'('#skF_2', '#skF_3')) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_74))) | ~v1_funct_2(C_75, '#skF_2', B_74) | ~v1_funct_1(C_75))), inference(negUnitSimplification, [status(thm)], [c_50, c_200])).
% 2.24/1.28  tff(c_213, plain, (k3_funct_2('#skF_2', '#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3'))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_210])).
% 2.24/1.28  tff(c_216, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3'))='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_182, c_213])).
% 2.24/1.28  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_216])).
% 2.24/1.28  tff(c_219, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_101])).
% 2.24/1.28  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.24/1.28  tff(c_226, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_2])).
% 2.24/1.28  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_226])).
% 2.24/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.28  
% 2.24/1.28  Inference rules
% 2.24/1.28  ----------------------
% 2.24/1.28  #Ref     : 0
% 2.24/1.28  #Sup     : 32
% 2.24/1.28  #Fact    : 0
% 2.24/1.28  #Define  : 0
% 2.24/1.28  #Split   : 2
% 2.24/1.28  #Chain   : 0
% 2.24/1.28  #Close   : 0
% 2.24/1.28  
% 2.24/1.28  Ordering : KBO
% 2.24/1.28  
% 2.24/1.28  Simplification rules
% 2.24/1.28  ----------------------
% 2.24/1.28  #Subsume      : 0
% 2.24/1.28  #Demod        : 75
% 2.24/1.28  #Tautology    : 20
% 2.24/1.28  #SimpNegUnit  : 8
% 2.24/1.28  #BackRed      : 8
% 2.24/1.28  
% 2.24/1.28  #Partial instantiations: 0
% 2.24/1.28  #Strategies tried      : 1
% 2.24/1.28  
% 2.24/1.28  Timing (in seconds)
% 2.24/1.28  ----------------------
% 2.41/1.28  Preprocessing        : 0.32
% 2.41/1.28  Parsing              : 0.17
% 2.41/1.28  CNF conversion       : 0.02
% 2.41/1.28  Main loop            : 0.19
% 2.41/1.28  Inferencing          : 0.06
% 2.41/1.28  Reduction            : 0.07
% 2.41/1.28  Demodulation         : 0.05
% 2.41/1.28  BG Simplification    : 0.02
% 2.41/1.28  Subsumption          : 0.03
% 2.41/1.28  Abstraction          : 0.01
% 2.41/1.28  MUC search           : 0.00
% 2.41/1.28  Cooper               : 0.00
% 2.41/1.28  Total                : 0.54
% 2.41/1.28  Index Insertion      : 0.00
% 2.41/1.28  Index Deletion       : 0.00
% 2.41/1.28  Index Matching       : 0.00
% 2.41/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
