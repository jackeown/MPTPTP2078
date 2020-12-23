%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:01 EST 2020

% Result     : Theorem 4.64s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 330 expanded)
%              Number of leaves         :   45 ( 139 expanded)
%              Depth                    :   10
%              Number of atoms          :  215 (1038 expanded)
%              Number of equality atoms :   30 (  97 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_179,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_120,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_98,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_159,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_20,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_149,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_161,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_149])).

tff(c_173,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_161])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_185,plain,(
    ! [A_68] :
      ( v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68)
      | ~ v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_62,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_132,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_188,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_185,c_132])).

tff(c_191,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_76,c_188])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_54,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    ! [A_18] : v2_funct_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_78,plain,(
    ! [A_18] : v2_funct_1(k6_partfun1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_32])).

tff(c_50,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] :
      ( m1_subset_1(k1_partfun1(A_32,B_33,C_34,D_35,E_36,F_37),k1_zfmisc_1(k2_zfmisc_1(A_32,D_35)))
      | ~ m1_subset_1(F_37,k1_zfmisc_1(k2_zfmisc_1(C_34,D_35)))
      | ~ v1_funct_1(F_37)
      | ~ m1_subset_1(E_36,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_1(E_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    ! [A_29] : m1_subset_1(k6_relat_1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_77,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_44])).

tff(c_64,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_913,plain,(
    ! [D_195,C_196,A_197,B_198] :
      ( D_195 = C_196
      | ~ r2_relset_1(A_197,B_198,C_196,D_195)
      | ~ m1_subset_1(D_195,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_923,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_64,c_913])).

tff(c_942,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_923])).

tff(c_1179,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_942])).

tff(c_1182,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1179])).

tff(c_1186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_1182])).

tff(c_1187,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_942])).

tff(c_1203,plain,(
    ! [D_253,E_256,A_257,B_255,C_254] :
      ( k1_xboole_0 = C_254
      | v2_funct_1(D_253)
      | ~ v2_funct_1(k1_partfun1(A_257,B_255,B_255,C_254,D_253,E_256))
      | ~ m1_subset_1(E_256,k1_zfmisc_1(k2_zfmisc_1(B_255,C_254)))
      | ~ v1_funct_2(E_256,B_255,C_254)
      | ~ v1_funct_1(E_256)
      | ~ m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1(A_257,B_255)))
      | ~ v1_funct_2(D_253,A_257,B_255)
      | ~ v1_funct_1(D_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1205,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1187,c_1203])).

tff(c_1210,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_78,c_1205])).

tff(c_1211,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_1210])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1246,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1211,c_6])).

tff(c_12,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1245,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_2',B_6) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1211,c_1211,c_12])).

tff(c_212,plain,(
    ! [C_73,B_74,A_75] :
      ( ~ v1_xboole_0(C_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(C_73))
      | ~ r2_hidden(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_226,plain,(
    ! [A_75] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_75,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_212])).

tff(c_786,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_1289,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1245,c_786])).

tff(c_1293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1246,c_1289])).

tff(c_1296,plain,(
    ! [A_264] : ~ r2_hidden(A_264,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_1300,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_1296])).

tff(c_1304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_1300])).

tff(c_1305,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1335,plain,(
    ! [B_272,A_273] :
      ( v1_relat_1(B_272)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(A_273))
      | ~ v1_relat_1(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1347,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_1335])).

tff(c_1359,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1347])).

tff(c_1391,plain,(
    ! [C_278,B_279,A_280] :
      ( v5_relat_1(C_278,B_279)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_280,B_279))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1409,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1391])).

tff(c_1467,plain,(
    ! [A_296,B_297,D_298] :
      ( r2_relset_1(A_296,B_297,D_298,D_298)
      | ~ m1_subset_1(D_298,k1_zfmisc_1(k2_zfmisc_1(A_296,B_297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1478,plain,(
    ! [A_29] : r2_relset_1(A_29,A_29,k6_partfun1(A_29),k6_partfun1(A_29)) ),
    inference(resolution,[status(thm)],[c_77,c_1467])).

tff(c_1520,plain,(
    ! [A_307,B_308,C_309] :
      ( k2_relset_1(A_307,B_308,C_309) = k2_relat_1(C_309)
      | ~ m1_subset_1(C_309,k1_zfmisc_1(k2_zfmisc_1(A_307,B_308))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1538,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1520])).

tff(c_1556,plain,(
    ! [D_311,C_312,A_313,B_314] :
      ( D_311 = C_312
      | ~ r2_relset_1(A_313,B_314,C_312,D_311)
      | ~ m1_subset_1(D_311,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314)))
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1566,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_64,c_1556])).

tff(c_1585,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1566])).

tff(c_1770,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1585])).

tff(c_1773,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1770])).

tff(c_1777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_1773])).

tff(c_1778,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1585])).

tff(c_1919,plain,(
    ! [A_399,B_400,C_401,D_402] :
      ( k2_relset_1(A_399,B_400,C_401) = B_400
      | ~ r2_relset_1(B_400,B_400,k1_partfun1(B_400,A_399,A_399,B_400,D_402,C_401),k6_partfun1(B_400))
      | ~ m1_subset_1(D_402,k1_zfmisc_1(k2_zfmisc_1(B_400,A_399)))
      | ~ v1_funct_2(D_402,B_400,A_399)
      | ~ v1_funct_1(D_402)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_399,B_400)))
      | ~ v1_funct_2(C_401,A_399,B_400)
      | ~ v1_funct_1(C_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1922,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1778,c_1919])).

tff(c_1924,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_1478,c_1538,c_1922])).

tff(c_46,plain,(
    ! [B_31] :
      ( v2_funct_2(B_31,k2_relat_1(B_31))
      | ~ v5_relat_1(B_31,k2_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1929,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1924,c_46])).

tff(c_1933,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_1409,c_1924,c_1929])).

tff(c_1935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1305,c_1933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:46:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.64/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.76  
% 4.64/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.76  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.64/1.76  
% 4.64/1.76  %Foreground sorts:
% 4.64/1.76  
% 4.64/1.76  
% 4.64/1.76  %Background operators:
% 4.64/1.76  
% 4.64/1.76  
% 4.64/1.76  %Foreground operators:
% 4.64/1.76  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.64/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.64/1.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.64/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.64/1.76  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.64/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.64/1.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.64/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.64/1.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.64/1.76  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.64/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.64/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.64/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.64/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.64/1.76  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.64/1.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.64/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.64/1.76  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.64/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.64/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.64/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.64/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.64/1.76  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.64/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.64/1.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.64/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.64/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.64/1.76  
% 4.64/1.78  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.64/1.78  tff(f_179, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 4.64/1.78  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.64/1.78  tff(f_74, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 4.64/1.78  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.64/1.78  tff(f_120, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.64/1.78  tff(f_78, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.64/1.78  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.64/1.78  tff(f_98, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.64/1.78  tff(f_96, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.64/1.78  tff(f_159, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 4.64/1.78  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.64/1.78  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.64/1.78  tff(f_45, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.64/1.78  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.64/1.78  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.64/1.78  tff(f_137, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.64/1.78  tff(f_106, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.64/1.78  tff(c_20, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.64/1.78  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.64/1.78  tff(c_149, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.64/1.78  tff(c_161, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_149])).
% 4.64/1.78  tff(c_173, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_161])).
% 4.64/1.78  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.64/1.78  tff(c_185, plain, (![A_68]: (v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68) | ~v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.64/1.78  tff(c_62, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.64/1.78  tff(c_132, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 4.64/1.78  tff(c_188, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_185, c_132])).
% 4.64/1.78  tff(c_191, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_76, c_188])).
% 4.64/1.78  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.64/1.78  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.64/1.78  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.64/1.78  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.64/1.78  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.64/1.78  tff(c_54, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.64/1.78  tff(c_32, plain, (![A_18]: (v2_funct_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.64/1.78  tff(c_78, plain, (![A_18]: (v2_funct_1(k6_partfun1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_32])).
% 4.64/1.78  tff(c_50, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (m1_subset_1(k1_partfun1(A_32, B_33, C_34, D_35, E_36, F_37), k1_zfmisc_1(k2_zfmisc_1(A_32, D_35))) | ~m1_subset_1(F_37, k1_zfmisc_1(k2_zfmisc_1(C_34, D_35))) | ~v1_funct_1(F_37) | ~m1_subset_1(E_36, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_1(E_36))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.64/1.78  tff(c_44, plain, (![A_29]: (m1_subset_1(k6_relat_1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.64/1.78  tff(c_77, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_44])).
% 4.64/1.78  tff(c_64, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.64/1.78  tff(c_913, plain, (![D_195, C_196, A_197, B_198]: (D_195=C_196 | ~r2_relset_1(A_197, B_198, C_196, D_195) | ~m1_subset_1(D_195, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.64/1.78  tff(c_923, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_64, c_913])).
% 4.64/1.78  tff(c_942, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_923])).
% 4.64/1.78  tff(c_1179, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_942])).
% 4.64/1.78  tff(c_1182, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1179])).
% 4.64/1.78  tff(c_1186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_1182])).
% 4.64/1.78  tff(c_1187, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_942])).
% 4.64/1.78  tff(c_1203, plain, (![D_253, E_256, A_257, B_255, C_254]: (k1_xboole_0=C_254 | v2_funct_1(D_253) | ~v2_funct_1(k1_partfun1(A_257, B_255, B_255, C_254, D_253, E_256)) | ~m1_subset_1(E_256, k1_zfmisc_1(k2_zfmisc_1(B_255, C_254))) | ~v1_funct_2(E_256, B_255, C_254) | ~v1_funct_1(E_256) | ~m1_subset_1(D_253, k1_zfmisc_1(k2_zfmisc_1(A_257, B_255))) | ~v1_funct_2(D_253, A_257, B_255) | ~v1_funct_1(D_253))), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.64/1.78  tff(c_1205, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1187, c_1203])).
% 4.64/1.78  tff(c_1210, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_78, c_1205])).
% 4.64/1.78  tff(c_1211, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_132, c_1210])).
% 4.64/1.78  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.64/1.78  tff(c_1246, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1211, c_6])).
% 4.64/1.78  tff(c_12, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.64/1.78  tff(c_1245, plain, (![B_6]: (k2_zfmisc_1('#skF_2', B_6)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1211, c_1211, c_12])).
% 4.64/1.78  tff(c_212, plain, (![C_73, B_74, A_75]: (~v1_xboole_0(C_73) | ~m1_subset_1(B_74, k1_zfmisc_1(C_73)) | ~r2_hidden(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.64/1.78  tff(c_226, plain, (![A_75]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_75, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_212])).
% 4.64/1.78  tff(c_786, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_226])).
% 4.64/1.78  tff(c_1289, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1245, c_786])).
% 4.64/1.78  tff(c_1293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1246, c_1289])).
% 4.64/1.78  tff(c_1296, plain, (![A_264]: (~r2_hidden(A_264, '#skF_4'))), inference(splitRight, [status(thm)], [c_226])).
% 4.64/1.78  tff(c_1300, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_1296])).
% 4.64/1.78  tff(c_1304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_1300])).
% 4.64/1.78  tff(c_1305, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 4.64/1.78  tff(c_1335, plain, (![B_272, A_273]: (v1_relat_1(B_272) | ~m1_subset_1(B_272, k1_zfmisc_1(A_273)) | ~v1_relat_1(A_273))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.64/1.78  tff(c_1347, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_1335])).
% 4.64/1.78  tff(c_1359, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1347])).
% 4.64/1.78  tff(c_1391, plain, (![C_278, B_279, A_280]: (v5_relat_1(C_278, B_279) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_280, B_279))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.64/1.78  tff(c_1409, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_1391])).
% 4.64/1.78  tff(c_1467, plain, (![A_296, B_297, D_298]: (r2_relset_1(A_296, B_297, D_298, D_298) | ~m1_subset_1(D_298, k1_zfmisc_1(k2_zfmisc_1(A_296, B_297))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.64/1.78  tff(c_1478, plain, (![A_29]: (r2_relset_1(A_29, A_29, k6_partfun1(A_29), k6_partfun1(A_29)))), inference(resolution, [status(thm)], [c_77, c_1467])).
% 4.64/1.78  tff(c_1520, plain, (![A_307, B_308, C_309]: (k2_relset_1(A_307, B_308, C_309)=k2_relat_1(C_309) | ~m1_subset_1(C_309, k1_zfmisc_1(k2_zfmisc_1(A_307, B_308))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.64/1.78  tff(c_1538, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1520])).
% 4.64/1.78  tff(c_1556, plain, (![D_311, C_312, A_313, B_314]: (D_311=C_312 | ~r2_relset_1(A_313, B_314, C_312, D_311) | ~m1_subset_1(D_311, k1_zfmisc_1(k2_zfmisc_1(A_313, B_314))) | ~m1_subset_1(C_312, k1_zfmisc_1(k2_zfmisc_1(A_313, B_314))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.64/1.78  tff(c_1566, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_64, c_1556])).
% 4.64/1.78  tff(c_1585, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1566])).
% 4.64/1.78  tff(c_1770, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1585])).
% 4.64/1.78  tff(c_1773, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1770])).
% 4.64/1.78  tff(c_1777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_1773])).
% 4.64/1.78  tff(c_1778, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1585])).
% 4.64/1.78  tff(c_1919, plain, (![A_399, B_400, C_401, D_402]: (k2_relset_1(A_399, B_400, C_401)=B_400 | ~r2_relset_1(B_400, B_400, k1_partfun1(B_400, A_399, A_399, B_400, D_402, C_401), k6_partfun1(B_400)) | ~m1_subset_1(D_402, k1_zfmisc_1(k2_zfmisc_1(B_400, A_399))) | ~v1_funct_2(D_402, B_400, A_399) | ~v1_funct_1(D_402) | ~m1_subset_1(C_401, k1_zfmisc_1(k2_zfmisc_1(A_399, B_400))) | ~v1_funct_2(C_401, A_399, B_400) | ~v1_funct_1(C_401))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.64/1.78  tff(c_1922, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1778, c_1919])).
% 4.64/1.78  tff(c_1924, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_1478, c_1538, c_1922])).
% 4.64/1.78  tff(c_46, plain, (![B_31]: (v2_funct_2(B_31, k2_relat_1(B_31)) | ~v5_relat_1(B_31, k2_relat_1(B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.64/1.78  tff(c_1929, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1924, c_46])).
% 4.64/1.78  tff(c_1933, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_1409, c_1924, c_1929])).
% 4.64/1.78  tff(c_1935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1305, c_1933])).
% 4.64/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.78  
% 4.64/1.78  Inference rules
% 4.64/1.78  ----------------------
% 4.64/1.78  #Ref     : 0
% 4.64/1.78  #Sup     : 386
% 4.64/1.78  #Fact    : 0
% 4.64/1.78  #Define  : 0
% 4.64/1.78  #Split   : 14
% 4.64/1.78  #Chain   : 0
% 4.64/1.78  #Close   : 0
% 4.64/1.78  
% 4.64/1.78  Ordering : KBO
% 4.64/1.78  
% 4.64/1.78  Simplification rules
% 4.64/1.78  ----------------------
% 4.64/1.78  #Subsume      : 13
% 4.64/1.78  #Demod        : 361
% 4.64/1.78  #Tautology    : 130
% 4.64/1.78  #SimpNegUnit  : 4
% 4.64/1.78  #BackRed      : 79
% 4.64/1.78  
% 4.64/1.78  #Partial instantiations: 0
% 4.64/1.78  #Strategies tried      : 1
% 4.64/1.78  
% 4.64/1.78  Timing (in seconds)
% 4.64/1.78  ----------------------
% 4.64/1.78  Preprocessing        : 0.36
% 4.64/1.79  Parsing              : 0.19
% 4.64/1.79  CNF conversion       : 0.03
% 4.64/1.79  Main loop            : 0.72
% 4.64/1.79  Inferencing          : 0.26
% 4.64/1.79  Reduction            : 0.25
% 4.64/1.79  Demodulation         : 0.18
% 4.64/1.79  BG Simplification    : 0.03
% 4.64/1.79  Subsumption          : 0.12
% 4.64/1.79  Abstraction          : 0.03
% 4.64/1.79  MUC search           : 0.00
% 4.64/1.79  Cooper               : 0.00
% 4.64/1.79  Total                : 1.12
% 4.64/1.79  Index Insertion      : 0.00
% 4.64/1.79  Index Deletion       : 0.00
% 4.64/1.79  Index Matching       : 0.00
% 4.64/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
