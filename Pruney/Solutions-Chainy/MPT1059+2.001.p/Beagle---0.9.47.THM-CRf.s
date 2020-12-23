%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:33 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 112 expanded)
%              Number of leaves         :   39 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  124 ( 277 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_221,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_201,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_92,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_177,axiom,(
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

tff(f_188,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_102,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_100,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_98,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_96,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_104,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_94,plain,(
    m1_subset_1('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_1887,plain,(
    ! [A_224,B_225,C_226,D_227] :
      ( k3_funct_2(A_224,B_225,C_226,D_227) = k1_funct_1(C_226,D_227)
      | ~ m1_subset_1(D_227,A_224)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225)))
      | ~ v1_funct_2(C_226,A_224,B_225)
      | ~ v1_funct_1(C_226)
      | v1_xboole_0(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_1893,plain,(
    ! [B_225,C_226] :
      ( k3_funct_2('#skF_3',B_225,C_226,'#skF_6') = k1_funct_1(C_226,'#skF_6')
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_225)))
      | ~ v1_funct_2(C_226,'#skF_3',B_225)
      | ~ v1_funct_1(C_226)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_94,c_1887])).

tff(c_2231,plain,(
    ! [B_253,C_254] :
      ( k3_funct_2('#skF_3',B_253,C_254,'#skF_6') = k1_funct_1(C_254,'#skF_6')
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_253)))
      | ~ v1_funct_2(C_254,'#skF_3',B_253)
      | ~ v1_funct_1(C_254) ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1893])).

tff(c_2242,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_2231])).

tff(c_2246,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_2242])).

tff(c_92,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_6') != k7_partfun1('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_2247,plain,(
    k7_partfun1('#skF_4','#skF_5','#skF_6') != k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2246,c_92])).

tff(c_845,plain,(
    ! [C_132,B_133,A_134] :
      ( v5_relat_1(C_132,B_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_134,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_860,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_845])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_42,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_682,plain,(
    ! [B_113,A_114] :
      ( v1_relat_1(B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_114))
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_689,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_96,c_682])).

tff(c_693,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_689])).

tff(c_964,plain,(
    ! [A_145,B_146,C_147] :
      ( k1_relset_1(A_145,B_146,C_147) = k1_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_979,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_964])).

tff(c_1187,plain,(
    ! [B_169,A_170,C_171] :
      ( k1_xboole_0 = B_169
      | k1_relset_1(A_170,B_169,C_171) = A_170
      | ~ v1_funct_2(C_171,A_170,B_169)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_170,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_1197,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_1187])).

tff(c_1205,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_979,c_1197])).

tff(c_1206,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1205])).

tff(c_1514,plain,(
    ! [A_194,B_195,C_196] :
      ( k7_partfun1(A_194,B_195,C_196) = k1_funct_1(B_195,C_196)
      | ~ r2_hidden(C_196,k1_relat_1(B_195))
      | ~ v1_funct_1(B_195)
      | ~ v5_relat_1(B_195,A_194)
      | ~ v1_relat_1(B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1516,plain,(
    ! [A_194,C_196] :
      ( k7_partfun1(A_194,'#skF_5',C_196) = k1_funct_1('#skF_5',C_196)
      | ~ r2_hidden(C_196,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_194)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1206,c_1514])).

tff(c_1746,plain,(
    ! [A_214,C_215] :
      ( k7_partfun1(A_214,'#skF_5',C_215) = k1_funct_1('#skF_5',C_215)
      | ~ r2_hidden(C_215,'#skF_3')
      | ~ v5_relat_1('#skF_5',A_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_100,c_1516])).

tff(c_1752,plain,(
    ! [A_214,B_12] :
      ( k7_partfun1(A_214,'#skF_5',B_12) = k1_funct_1('#skF_5',B_12)
      | ~ v5_relat_1('#skF_5',A_214)
      | ~ m1_subset_1(B_12,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_1746])).

tff(c_1933,plain,(
    ! [A_232,B_233] :
      ( k7_partfun1(A_232,'#skF_5',B_233) = k1_funct_1('#skF_5',B_233)
      | ~ v5_relat_1('#skF_5',A_232)
      | ~ m1_subset_1(B_233,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1752])).

tff(c_2405,plain,(
    ! [B_270] :
      ( k7_partfun1('#skF_4','#skF_5',B_270) = k1_funct_1('#skF_5',B_270)
      | ~ m1_subset_1(B_270,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_860,c_1933])).

tff(c_2416,plain,(
    k7_partfun1('#skF_4','#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_2405])).

tff(c_2424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2247,c_2416])).

tff(c_2425,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1205])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2474,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2425,c_8])).

tff(c_2476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_2474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.81  
% 4.55/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.81  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.55/1.81  
% 4.55/1.81  %Foreground sorts:
% 4.55/1.81  
% 4.55/1.81  
% 4.55/1.81  %Background operators:
% 4.55/1.81  
% 4.55/1.81  
% 4.55/1.81  %Foreground operators:
% 4.55/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.55/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.55/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.55/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.55/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.55/1.81  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.55/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.55/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.55/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.55/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.55/1.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.55/1.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.55/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.55/1.81  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 4.55/1.81  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.55/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.55/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.55/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.55/1.81  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.55/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.55/1.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.55/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.55/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.55/1.81  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.55/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.55/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.55/1.81  
% 4.55/1.82  tff(f_221, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 4.55/1.82  tff(f_201, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.55/1.82  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.55/1.82  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.55/1.82  tff(f_92, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.55/1.82  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.55/1.82  tff(f_139, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.55/1.82  tff(f_177, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.55/1.82  tff(f_188, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 4.55/1.82  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.55/1.82  tff(c_102, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.55/1.82  tff(c_100, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.55/1.82  tff(c_98, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.55/1.82  tff(c_96, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.55/1.82  tff(c_104, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.55/1.82  tff(c_94, plain, (m1_subset_1('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.55/1.82  tff(c_1887, plain, (![A_224, B_225, C_226, D_227]: (k3_funct_2(A_224, B_225, C_226, D_227)=k1_funct_1(C_226, D_227) | ~m1_subset_1(D_227, A_224) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))) | ~v1_funct_2(C_226, A_224, B_225) | ~v1_funct_1(C_226) | v1_xboole_0(A_224))), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.55/1.82  tff(c_1893, plain, (![B_225, C_226]: (k3_funct_2('#skF_3', B_225, C_226, '#skF_6')=k1_funct_1(C_226, '#skF_6') | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_225))) | ~v1_funct_2(C_226, '#skF_3', B_225) | ~v1_funct_1(C_226) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_94, c_1887])).
% 4.55/1.82  tff(c_2231, plain, (![B_253, C_254]: (k3_funct_2('#skF_3', B_253, C_254, '#skF_6')=k1_funct_1(C_254, '#skF_6') | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_253))) | ~v1_funct_2(C_254, '#skF_3', B_253) | ~v1_funct_1(C_254))), inference(negUnitSimplification, [status(thm)], [c_104, c_1893])).
% 4.55/1.82  tff(c_2242, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_2231])).
% 4.55/1.82  tff(c_2246, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_2242])).
% 4.55/1.82  tff(c_92, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k7_partfun1('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.55/1.82  tff(c_2247, plain, (k7_partfun1('#skF_4', '#skF_5', '#skF_6')!=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2246, c_92])).
% 4.55/1.82  tff(c_845, plain, (![C_132, B_133, A_134]: (v5_relat_1(C_132, B_133) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_134, B_133))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.55/1.82  tff(c_860, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_96, c_845])).
% 4.55/1.82  tff(c_26, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.55/1.82  tff(c_42, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.55/1.82  tff(c_682, plain, (![B_113, A_114]: (v1_relat_1(B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(A_114)) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.55/1.82  tff(c_689, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_96, c_682])).
% 4.55/1.82  tff(c_693, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_689])).
% 4.55/1.82  tff(c_964, plain, (![A_145, B_146, C_147]: (k1_relset_1(A_145, B_146, C_147)=k1_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.55/1.82  tff(c_979, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_964])).
% 4.55/1.82  tff(c_1187, plain, (![B_169, A_170, C_171]: (k1_xboole_0=B_169 | k1_relset_1(A_170, B_169, C_171)=A_170 | ~v1_funct_2(C_171, A_170, B_169) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_170, B_169))))), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.55/1.82  tff(c_1197, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_96, c_1187])).
% 4.55/1.82  tff(c_1205, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_979, c_1197])).
% 4.55/1.82  tff(c_1206, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1205])).
% 4.55/1.82  tff(c_1514, plain, (![A_194, B_195, C_196]: (k7_partfun1(A_194, B_195, C_196)=k1_funct_1(B_195, C_196) | ~r2_hidden(C_196, k1_relat_1(B_195)) | ~v1_funct_1(B_195) | ~v5_relat_1(B_195, A_194) | ~v1_relat_1(B_195))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.55/1.82  tff(c_1516, plain, (![A_194, C_196]: (k7_partfun1(A_194, '#skF_5', C_196)=k1_funct_1('#skF_5', C_196) | ~r2_hidden(C_196, '#skF_3') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_194) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1206, c_1514])).
% 4.55/1.82  tff(c_1746, plain, (![A_214, C_215]: (k7_partfun1(A_214, '#skF_5', C_215)=k1_funct_1('#skF_5', C_215) | ~r2_hidden(C_215, '#skF_3') | ~v5_relat_1('#skF_5', A_214))), inference(demodulation, [status(thm), theory('equality')], [c_693, c_100, c_1516])).
% 4.55/1.82  tff(c_1752, plain, (![A_214, B_12]: (k7_partfun1(A_214, '#skF_5', B_12)=k1_funct_1('#skF_5', B_12) | ~v5_relat_1('#skF_5', A_214) | ~m1_subset_1(B_12, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_1746])).
% 4.55/1.82  tff(c_1933, plain, (![A_232, B_233]: (k7_partfun1(A_232, '#skF_5', B_233)=k1_funct_1('#skF_5', B_233) | ~v5_relat_1('#skF_5', A_232) | ~m1_subset_1(B_233, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_104, c_1752])).
% 4.55/1.82  tff(c_2405, plain, (![B_270]: (k7_partfun1('#skF_4', '#skF_5', B_270)=k1_funct_1('#skF_5', B_270) | ~m1_subset_1(B_270, '#skF_3'))), inference(resolution, [status(thm)], [c_860, c_1933])).
% 4.55/1.82  tff(c_2416, plain, (k7_partfun1('#skF_4', '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_94, c_2405])).
% 4.55/1.82  tff(c_2424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2247, c_2416])).
% 4.55/1.82  tff(c_2425, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1205])).
% 4.55/1.82  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.55/1.82  tff(c_2474, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2425, c_8])).
% 4.55/1.82  tff(c_2476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_2474])).
% 4.55/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.82  
% 4.55/1.82  Inference rules
% 4.55/1.82  ----------------------
% 4.55/1.82  #Ref     : 0
% 4.55/1.82  #Sup     : 508
% 4.55/1.82  #Fact    : 0
% 4.55/1.82  #Define  : 0
% 4.55/1.82  #Split   : 4
% 4.55/1.82  #Chain   : 0
% 4.55/1.82  #Close   : 0
% 4.55/1.82  
% 4.55/1.82  Ordering : KBO
% 4.55/1.82  
% 4.55/1.82  Simplification rules
% 4.55/1.82  ----------------------
% 4.55/1.82  #Subsume      : 170
% 4.55/1.82  #Demod        : 389
% 4.55/1.82  #Tautology    : 180
% 4.55/1.82  #SimpNegUnit  : 17
% 4.55/1.82  #BackRed      : 51
% 4.55/1.82  
% 4.55/1.82  #Partial instantiations: 0
% 4.55/1.82  #Strategies tried      : 1
% 4.55/1.82  
% 4.55/1.82  Timing (in seconds)
% 4.55/1.82  ----------------------
% 4.55/1.82  Preprocessing        : 0.37
% 4.55/1.82  Parsing              : 0.19
% 4.55/1.82  CNF conversion       : 0.03
% 4.55/1.82  Main loop            : 0.63
% 4.55/1.82  Inferencing          : 0.21
% 4.55/1.82  Reduction            : 0.22
% 4.55/1.83  Demodulation         : 0.15
% 4.55/1.83  BG Simplification    : 0.03
% 4.55/1.83  Subsumption          : 0.14
% 4.55/1.83  Abstraction          : 0.02
% 4.55/1.83  MUC search           : 0.00
% 4.80/1.83  Cooper               : 0.00
% 4.80/1.83  Total                : 1.04
% 4.80/1.83  Index Insertion      : 0.00
% 4.80/1.83  Index Deletion       : 0.00
% 4.80/1.83  Index Matching       : 0.00
% 4.80/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
