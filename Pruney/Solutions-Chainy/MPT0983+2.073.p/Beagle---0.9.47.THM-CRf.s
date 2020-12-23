%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:11 EST 2020

% Result     : Theorem 6.66s
% Output     : CNFRefutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :  184 (1250 expanded)
%              Number of leaves         :   42 ( 447 expanded)
%              Depth                    :   12
%              Number of atoms          :  360 (3898 expanded)
%              Number of equality atoms :   89 ( 598 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_95,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_89,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_134,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_112,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_56,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_112,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_48,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_22,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_71,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22])).

tff(c_40,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] :
      ( m1_subset_1(k1_partfun1(A_24,B_25,C_26,D_27,E_28,F_29),k1_zfmisc_1(k2_zfmisc_1(A_24,D_27)))
      | ~ m1_subset_1(F_29,k1_zfmisc_1(k2_zfmisc_1(C_26,D_27)))
      | ~ v1_funct_1(F_29)
      | ~ m1_subset_1(E_28,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_1(E_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_503,plain,(
    ! [D_102,C_103,A_104,B_105] :
      ( D_102 = C_103
      | ~ r2_relset_1(A_104,B_105,C_103,D_102)
      | ~ m1_subset_1(D_102,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_509,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_503])).

tff(c_520,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_509])).

tff(c_867,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_520])).

tff(c_962,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_867])).

tff(c_969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_962])).

tff(c_970,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_520])).

tff(c_1021,plain,(
    ! [B_183,D_184,E_185,A_182,C_186] :
      ( k1_xboole_0 = C_186
      | v2_funct_1(D_184)
      | ~ v2_funct_1(k1_partfun1(A_182,B_183,B_183,C_186,D_184,E_185))
      | ~ m1_subset_1(E_185,k1_zfmisc_1(k2_zfmisc_1(B_183,C_186)))
      | ~ v1_funct_2(E_185,B_183,C_186)
      | ~ v1_funct_1(E_185)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ v1_funct_2(D_184,A_182,B_183)
      | ~ v1_funct_1(D_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1023,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_1021])).

tff(c_1025,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_71,c_1023])).

tff(c_1026,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_1025])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1056,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1054,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_1026,c_12])).

tff(c_124,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_143,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_124])).

tff(c_145,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(B_57,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_143,c_145])).

tff(c_245,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_1160,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_245])).

tff(c_1165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1056,c_1160])).

tff(c_1166,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_1169,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1166,c_60])).

tff(c_1639,plain,(
    ! [D_254,C_255,A_256,B_257] :
      ( D_254 = C_255
      | ~ r2_relset_1(A_256,B_257,C_255,D_254)
      | ~ m1_subset_1(D_254,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257)))
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1649,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_1639])).

tff(c_1668,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1649])).

tff(c_1688,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1668])).

tff(c_1921,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1688])).

tff(c_1928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_1169,c_1166,c_1921])).

tff(c_1929,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1668])).

tff(c_2323,plain,(
    ! [A_361,E_364,C_365,D_363,B_362] :
      ( k1_xboole_0 = C_365
      | v2_funct_1(D_363)
      | ~ v2_funct_1(k1_partfun1(A_361,B_362,B_362,C_365,D_363,E_364))
      | ~ m1_subset_1(E_364,k1_zfmisc_1(k2_zfmisc_1(B_362,C_365)))
      | ~ v1_funct_2(E_364,B_362,C_365)
      | ~ v1_funct_1(E_364)
      | ~ m1_subset_1(D_363,k1_zfmisc_1(k2_zfmisc_1(A_361,B_362)))
      | ~ v1_funct_2(D_363,A_361,B_362)
      | ~ v1_funct_1(D_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2325,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1929,c_2323])).

tff(c_2327,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_1169,c_1166,c_71,c_2325])).

tff(c_2328,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_2327])).

tff(c_2364,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2328,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2363,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2328,c_2328,c_14])).

tff(c_144,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_124])).

tff(c_156,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_144,c_145])).

tff(c_184,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_2496,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2363,c_184])).

tff(c_2501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_2496])).

tff(c_2502,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_3922,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2502,c_66])).

tff(c_2529,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2502,c_66])).

tff(c_3017,plain,(
    ! [D_439,C_440,A_441,B_442] :
      ( D_439 = C_440
      | ~ r2_relset_1(A_441,B_442,C_440,D_439)
      | ~ m1_subset_1(D_439,k1_zfmisc_1(k2_zfmisc_1(A_441,B_442)))
      | ~ m1_subset_1(C_440,k1_zfmisc_1(k2_zfmisc_1(A_441,B_442))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3027,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_3017])).

tff(c_3046,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3027])).

tff(c_3077,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3046])).

tff(c_3320,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_3077])).

tff(c_3327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2529,c_2502,c_64,c_60,c_3320])).

tff(c_3328,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3046])).

tff(c_3729,plain,(
    ! [B_549,A_548,D_550,E_551,C_552] :
      ( k1_xboole_0 = C_552
      | v2_funct_1(D_550)
      | ~ v2_funct_1(k1_partfun1(A_548,B_549,B_549,C_552,D_550,E_551))
      | ~ m1_subset_1(E_551,k1_zfmisc_1(k2_zfmisc_1(B_549,C_552)))
      | ~ v1_funct_2(E_551,B_549,C_552)
      | ~ v1_funct_1(E_551)
      | ~ m1_subset_1(D_550,k1_zfmisc_1(k2_zfmisc_1(A_548,B_549)))
      | ~ v1_funct_2(D_550,A_548,B_549)
      | ~ v1_funct_1(D_550) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3731,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3328,c_3729])).

tff(c_3733,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_2529,c_2502,c_64,c_62,c_60,c_71,c_3731])).

tff(c_3734,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_3733])).

tff(c_3770,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3734,c_8])).

tff(c_3768,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3734,c_3734,c_12])).

tff(c_2527,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_3902,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3768,c_2527])).

tff(c_3907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3770,c_3902])).

tff(c_3908,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_3934,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3908,c_60])).

tff(c_4609,plain,(
    ! [C_658,D_663,F_661,B_659,A_662,E_660] :
      ( m1_subset_1(k1_partfun1(A_662,B_659,C_658,D_663,E_660,F_661),k1_zfmisc_1(k2_zfmisc_1(A_662,D_663)))
      | ~ m1_subset_1(F_661,k1_zfmisc_1(k2_zfmisc_1(C_658,D_663)))
      | ~ v1_funct_1(F_661)
      | ~ m1_subset_1(E_660,k1_zfmisc_1(k2_zfmisc_1(A_662,B_659)))
      | ~ v1_funct_1(E_660) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4448,plain,(
    ! [D_629,C_630,A_631,B_632] :
      ( D_629 = C_630
      | ~ r2_relset_1(A_631,B_632,C_630,D_629)
      | ~ m1_subset_1(D_629,k1_zfmisc_1(k2_zfmisc_1(A_631,B_632)))
      | ~ m1_subset_1(C_630,k1_zfmisc_1(k2_zfmisc_1(A_631,B_632))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4456,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_4448])).

tff(c_4471,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4456])).

tff(c_4494,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4471])).

tff(c_4612,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4609,c_4494])).

tff(c_4647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3922,c_2502,c_64,c_3934,c_3908,c_4612])).

tff(c_4648,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4471])).

tff(c_5093,plain,(
    ! [D_731,A_729,C_733,B_730,E_732] :
      ( k1_xboole_0 = C_733
      | v2_funct_1(D_731)
      | ~ v2_funct_1(k1_partfun1(A_729,B_730,B_730,C_733,D_731,E_732))
      | ~ m1_subset_1(E_732,k1_zfmisc_1(k2_zfmisc_1(B_730,C_733)))
      | ~ v1_funct_2(E_732,B_730,C_733)
      | ~ v1_funct_1(E_732)
      | ~ m1_subset_1(D_731,k1_zfmisc_1(k2_zfmisc_1(A_729,B_730)))
      | ~ v1_funct_2(D_731,A_729,B_730)
      | ~ v1_funct_1(D_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_5095,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4648,c_5093])).

tff(c_5097,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3922,c_2502,c_64,c_62,c_3934,c_3908,c_71,c_5095])).

tff(c_5098,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_5097])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3939,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3908,c_10])).

tff(c_4013,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3939])).

tff(c_5122,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5098,c_4013])).

tff(c_5294,plain,(
    ! [A_744] : k2_zfmisc_1(A_744,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5098,c_5098,c_12])).

tff(c_5358,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5294,c_3908])).

tff(c_5382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5122,c_5358])).

tff(c_5384,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3939])).

tff(c_114,plain,(
    ! [A_54] : m1_subset_1(k6_partfun1(A_54),k1_zfmisc_1(k2_zfmisc_1(A_54,A_54))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_118,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_114])).

tff(c_140,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_118,c_124])).

tff(c_151,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_140,c_145])).

tff(c_160,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_151])).

tff(c_179,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_71])).

tff(c_5413,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5384,c_179])).

tff(c_5416,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5384,c_5384,c_12])).

tff(c_5417,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5384,c_5384,c_14])).

tff(c_5383,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3939])).

tff(c_5466,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5384,c_5384,c_5383])).

tff(c_5467,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5466])).

tff(c_5480,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5467,c_2502])).

tff(c_5549,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5417,c_5480])).

tff(c_5554,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5549,c_112])).

tff(c_5560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5413,c_5554])).

tff(c_5561,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5466])).

tff(c_5564,plain,(
    k2_zfmisc_1('#skF_1','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5561,c_2502])).

tff(c_5617,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5416,c_5564])).

tff(c_5662,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5617,c_112])).

tff(c_5668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5413,c_5662])).

tff(c_5669,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5771,plain,(
    ! [C_773,A_774,B_775] :
      ( v1_relat_1(C_773)
      | ~ m1_subset_1(C_773,k1_zfmisc_1(k2_zfmisc_1(A_774,B_775))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5792,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_5771])).

tff(c_5814,plain,(
    ! [C_777,B_778,A_779] :
      ( v5_relat_1(C_777,B_778)
      | ~ m1_subset_1(C_777,k1_zfmisc_1(k2_zfmisc_1(A_779,B_778))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5836,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_5814])).

tff(c_5919,plain,(
    ! [A_793,B_794,D_795] :
      ( r2_relset_1(A_793,B_794,D_795,D_795)
      | ~ m1_subset_1(D_795,k1_zfmisc_1(k2_zfmisc_1(A_793,B_794))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5933,plain,(
    ! [A_30] : r2_relset_1(A_30,A_30,k6_partfun1(A_30),k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_46,c_5919])).

tff(c_5984,plain,(
    ! [A_804,B_805,C_806] :
      ( k2_relset_1(A_804,B_805,C_806) = k2_relat_1(C_806)
      | ~ m1_subset_1(C_806,k1_zfmisc_1(k2_zfmisc_1(A_804,B_805))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6006,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_5984])).

tff(c_6047,plain,(
    ! [D_810,C_811,A_812,B_813] :
      ( D_810 = C_811
      | ~ r2_relset_1(A_812,B_813,C_811,D_810)
      | ~ m1_subset_1(D_810,k1_zfmisc_1(k2_zfmisc_1(A_812,B_813)))
      | ~ m1_subset_1(C_811,k1_zfmisc_1(k2_zfmisc_1(A_812,B_813))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6053,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_6047])).

tff(c_6064,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6053])).

tff(c_6380,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_6064])).

tff(c_6487,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_6380])).

tff(c_6494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_6487])).

tff(c_6495,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_6064])).

tff(c_6670,plain,(
    ! [A_909,B_910,C_911,D_912] :
      ( k2_relset_1(A_909,B_910,C_911) = B_910
      | ~ r2_relset_1(B_910,B_910,k1_partfun1(B_910,A_909,A_909,B_910,D_912,C_911),k6_partfun1(B_910))
      | ~ m1_subset_1(D_912,k1_zfmisc_1(k2_zfmisc_1(B_910,A_909)))
      | ~ v1_funct_2(D_912,B_910,A_909)
      | ~ v1_funct_1(D_912)
      | ~ m1_subset_1(C_911,k1_zfmisc_1(k2_zfmisc_1(A_909,B_910)))
      | ~ v1_funct_2(C_911,A_909,B_910)
      | ~ v1_funct_1(C_911) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6673,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6495,c_6670])).

tff(c_6678,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_5933,c_6006,c_6673])).

tff(c_36,plain,(
    ! [B_23] :
      ( v2_funct_2(B_23,k2_relat_1(B_23))
      | ~ v5_relat_1(B_23,k2_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6687,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6678,c_36])).

tff(c_6694,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5792,c_5836,c_6678,c_6687])).

tff(c_6696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5669,c_6694])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:35:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.66/2.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.54  
% 6.66/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.54  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.66/2.54  
% 6.66/2.54  %Foreground sorts:
% 6.66/2.54  
% 6.66/2.54  
% 6.66/2.54  %Background operators:
% 6.66/2.54  
% 6.66/2.54  
% 6.66/2.54  %Foreground operators:
% 6.66/2.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.66/2.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.66/2.54  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.66/2.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.66/2.54  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.66/2.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.66/2.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.66/2.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.66/2.54  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.66/2.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.66/2.54  tff('#skF_2', type, '#skF_2': $i).
% 6.66/2.54  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.66/2.54  tff('#skF_3', type, '#skF_3': $i).
% 6.66/2.54  tff('#skF_1', type, '#skF_1': $i).
% 6.66/2.54  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.66/2.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.66/2.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.66/2.54  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.66/2.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.66/2.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.66/2.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.66/2.54  tff('#skF_4', type, '#skF_4': $i).
% 6.66/2.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.66/2.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.66/2.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.66/2.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.66/2.54  
% 6.66/2.58  tff(f_154, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 6.66/2.58  tff(f_95, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.66/2.58  tff(f_47, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.66/2.58  tff(f_89, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.66/2.58  tff(f_93, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.66/2.58  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.66/2.58  tff(f_134, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 6.66/2.58  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.66/2.58  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.66/2.58  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.66/2.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.66/2.58  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.66/2.58  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.66/2.58  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.66/2.58  tff(f_112, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 6.66/2.58  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.66/2.58  tff(c_56, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.66/2.58  tff(c_112, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 6.66/2.58  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.66/2.58  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.66/2.58  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.66/2.58  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.66/2.58  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.66/2.58  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.66/2.58  tff(c_48, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.66/2.58  tff(c_22, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.66/2.58  tff(c_71, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22])).
% 6.66/2.58  tff(c_40, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (m1_subset_1(k1_partfun1(A_24, B_25, C_26, D_27, E_28, F_29), k1_zfmisc_1(k2_zfmisc_1(A_24, D_27))) | ~m1_subset_1(F_29, k1_zfmisc_1(k2_zfmisc_1(C_26, D_27))) | ~v1_funct_1(F_29) | ~m1_subset_1(E_28, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_1(E_28))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.66/2.58  tff(c_46, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.66/2.58  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.66/2.58  tff(c_503, plain, (![D_102, C_103, A_104, B_105]: (D_102=C_103 | ~r2_relset_1(A_104, B_105, C_103, D_102) | ~m1_subset_1(D_102, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.66/2.58  tff(c_509, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_503])).
% 6.66/2.58  tff(c_520, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_509])).
% 6.66/2.58  tff(c_867, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_520])).
% 6.66/2.58  tff(c_962, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_867])).
% 6.66/2.58  tff(c_969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_962])).
% 6.66/2.58  tff(c_970, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_520])).
% 6.66/2.58  tff(c_1021, plain, (![B_183, D_184, E_185, A_182, C_186]: (k1_xboole_0=C_186 | v2_funct_1(D_184) | ~v2_funct_1(k1_partfun1(A_182, B_183, B_183, C_186, D_184, E_185)) | ~m1_subset_1(E_185, k1_zfmisc_1(k2_zfmisc_1(B_183, C_186))) | ~v1_funct_2(E_185, B_183, C_186) | ~v1_funct_1(E_185) | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~v1_funct_2(D_184, A_182, B_183) | ~v1_funct_1(D_184))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.66/2.58  tff(c_1023, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_970, c_1021])).
% 6.66/2.58  tff(c_1025, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_71, c_1023])).
% 6.66/2.58  tff(c_1026, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_112, c_1025])).
% 6.66/2.58  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.66/2.58  tff(c_1056, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1026, c_8])).
% 6.66/2.58  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.66/2.58  tff(c_1054, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1026, c_1026, c_12])).
% 6.66/2.58  tff(c_124, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.66/2.58  tff(c_143, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_124])).
% 6.66/2.58  tff(c_145, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(B_57, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.66/2.58  tff(c_157, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(resolution, [status(thm)], [c_143, c_145])).
% 6.66/2.58  tff(c_245, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(splitLeft, [status(thm)], [c_157])).
% 6.66/2.58  tff(c_1160, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1054, c_245])).
% 6.66/2.58  tff(c_1165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1056, c_1160])).
% 6.66/2.58  tff(c_1166, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_157])).
% 6.66/2.58  tff(c_1169, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1166, c_60])).
% 6.66/2.58  tff(c_1639, plain, (![D_254, C_255, A_256, B_257]: (D_254=C_255 | ~r2_relset_1(A_256, B_257, C_255, D_254) | ~m1_subset_1(D_254, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.66/2.58  tff(c_1649, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_1639])).
% 6.66/2.58  tff(c_1668, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1649])).
% 6.66/2.58  tff(c_1688, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1668])).
% 6.66/2.58  tff(c_1921, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1688])).
% 6.66/2.58  tff(c_1928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_1169, c_1166, c_1921])).
% 6.66/2.58  tff(c_1929, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1668])).
% 6.66/2.58  tff(c_2323, plain, (![A_361, E_364, C_365, D_363, B_362]: (k1_xboole_0=C_365 | v2_funct_1(D_363) | ~v2_funct_1(k1_partfun1(A_361, B_362, B_362, C_365, D_363, E_364)) | ~m1_subset_1(E_364, k1_zfmisc_1(k2_zfmisc_1(B_362, C_365))) | ~v1_funct_2(E_364, B_362, C_365) | ~v1_funct_1(E_364) | ~m1_subset_1(D_363, k1_zfmisc_1(k2_zfmisc_1(A_361, B_362))) | ~v1_funct_2(D_363, A_361, B_362) | ~v1_funct_1(D_363))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.66/2.58  tff(c_2325, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1929, c_2323])).
% 6.66/2.58  tff(c_2327, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_1169, c_1166, c_71, c_2325])).
% 6.66/2.58  tff(c_2328, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_112, c_2327])).
% 6.66/2.58  tff(c_2364, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2328, c_8])).
% 6.66/2.58  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.66/2.58  tff(c_2363, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2328, c_2328, c_14])).
% 6.66/2.58  tff(c_144, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_124])).
% 6.66/2.58  tff(c_156, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_144, c_145])).
% 6.66/2.58  tff(c_184, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_156])).
% 6.66/2.58  tff(c_2496, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2363, c_184])).
% 6.66/2.58  tff(c_2501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2364, c_2496])).
% 6.66/2.58  tff(c_2502, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_156])).
% 6.66/2.58  tff(c_3922, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2502, c_66])).
% 6.66/2.58  tff(c_2529, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2502, c_66])).
% 6.66/2.58  tff(c_3017, plain, (![D_439, C_440, A_441, B_442]: (D_439=C_440 | ~r2_relset_1(A_441, B_442, C_440, D_439) | ~m1_subset_1(D_439, k1_zfmisc_1(k2_zfmisc_1(A_441, B_442))) | ~m1_subset_1(C_440, k1_zfmisc_1(k2_zfmisc_1(A_441, B_442))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.66/2.58  tff(c_3027, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_3017])).
% 6.66/2.58  tff(c_3046, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3027])).
% 6.66/2.58  tff(c_3077, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_3046])).
% 6.66/2.58  tff(c_3320, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_3077])).
% 6.66/2.58  tff(c_3327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_2529, c_2502, c_64, c_60, c_3320])).
% 6.66/2.58  tff(c_3328, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_3046])).
% 6.66/2.58  tff(c_3729, plain, (![B_549, A_548, D_550, E_551, C_552]: (k1_xboole_0=C_552 | v2_funct_1(D_550) | ~v2_funct_1(k1_partfun1(A_548, B_549, B_549, C_552, D_550, E_551)) | ~m1_subset_1(E_551, k1_zfmisc_1(k2_zfmisc_1(B_549, C_552))) | ~v1_funct_2(E_551, B_549, C_552) | ~v1_funct_1(E_551) | ~m1_subset_1(D_550, k1_zfmisc_1(k2_zfmisc_1(A_548, B_549))) | ~v1_funct_2(D_550, A_548, B_549) | ~v1_funct_1(D_550))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.66/2.58  tff(c_3731, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3328, c_3729])).
% 6.66/2.58  tff(c_3733, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_2529, c_2502, c_64, c_62, c_60, c_71, c_3731])).
% 6.66/2.58  tff(c_3734, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_112, c_3733])).
% 6.66/2.58  tff(c_3770, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3734, c_8])).
% 6.66/2.58  tff(c_3768, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3734, c_3734, c_12])).
% 6.66/2.58  tff(c_2527, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(splitLeft, [status(thm)], [c_157])).
% 6.66/2.58  tff(c_3902, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3768, c_2527])).
% 6.66/2.58  tff(c_3907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3770, c_3902])).
% 6.66/2.58  tff(c_3908, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_157])).
% 6.66/2.58  tff(c_3934, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3908, c_60])).
% 6.66/2.58  tff(c_4609, plain, (![C_658, D_663, F_661, B_659, A_662, E_660]: (m1_subset_1(k1_partfun1(A_662, B_659, C_658, D_663, E_660, F_661), k1_zfmisc_1(k2_zfmisc_1(A_662, D_663))) | ~m1_subset_1(F_661, k1_zfmisc_1(k2_zfmisc_1(C_658, D_663))) | ~v1_funct_1(F_661) | ~m1_subset_1(E_660, k1_zfmisc_1(k2_zfmisc_1(A_662, B_659))) | ~v1_funct_1(E_660))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.66/2.58  tff(c_4448, plain, (![D_629, C_630, A_631, B_632]: (D_629=C_630 | ~r2_relset_1(A_631, B_632, C_630, D_629) | ~m1_subset_1(D_629, k1_zfmisc_1(k2_zfmisc_1(A_631, B_632))) | ~m1_subset_1(C_630, k1_zfmisc_1(k2_zfmisc_1(A_631, B_632))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.66/2.58  tff(c_4456, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_4448])).
% 6.66/2.58  tff(c_4471, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4456])).
% 6.66/2.58  tff(c_4494, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_4471])).
% 6.66/2.58  tff(c_4612, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4609, c_4494])).
% 6.66/2.58  tff(c_4647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_3922, c_2502, c_64, c_3934, c_3908, c_4612])).
% 6.66/2.58  tff(c_4648, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_4471])).
% 6.66/2.58  tff(c_5093, plain, (![D_731, A_729, C_733, B_730, E_732]: (k1_xboole_0=C_733 | v2_funct_1(D_731) | ~v2_funct_1(k1_partfun1(A_729, B_730, B_730, C_733, D_731, E_732)) | ~m1_subset_1(E_732, k1_zfmisc_1(k2_zfmisc_1(B_730, C_733))) | ~v1_funct_2(E_732, B_730, C_733) | ~v1_funct_1(E_732) | ~m1_subset_1(D_731, k1_zfmisc_1(k2_zfmisc_1(A_729, B_730))) | ~v1_funct_2(D_731, A_729, B_730) | ~v1_funct_1(D_731))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.66/2.58  tff(c_5095, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4648, c_5093])).
% 6.66/2.58  tff(c_5097, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3922, c_2502, c_64, c_62, c_3934, c_3908, c_71, c_5095])).
% 6.66/2.58  tff(c_5098, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_112, c_5097])).
% 6.66/2.58  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.66/2.58  tff(c_3939, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3908, c_10])).
% 6.66/2.58  tff(c_4013, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_3939])).
% 6.66/2.58  tff(c_5122, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5098, c_4013])).
% 6.66/2.58  tff(c_5294, plain, (![A_744]: (k2_zfmisc_1(A_744, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5098, c_5098, c_12])).
% 6.66/2.58  tff(c_5358, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5294, c_3908])).
% 6.66/2.58  tff(c_5382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5122, c_5358])).
% 6.66/2.58  tff(c_5384, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3939])).
% 6.66/2.58  tff(c_114, plain, (![A_54]: (m1_subset_1(k6_partfun1(A_54), k1_zfmisc_1(k2_zfmisc_1(A_54, A_54))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.66/2.58  tff(c_118, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_114])).
% 6.66/2.58  tff(c_140, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_118, c_124])).
% 6.66/2.58  tff(c_151, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_140, c_145])).
% 6.66/2.58  tff(c_160, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_151])).
% 6.66/2.58  tff(c_179, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_160, c_71])).
% 6.66/2.58  tff(c_5413, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5384, c_179])).
% 6.66/2.58  tff(c_5416, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5384, c_5384, c_12])).
% 6.66/2.58  tff(c_5417, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5384, c_5384, c_14])).
% 6.66/2.58  tff(c_5383, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_3939])).
% 6.66/2.58  tff(c_5466, plain, ('#skF_2'='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5384, c_5384, c_5383])).
% 6.66/2.58  tff(c_5467, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_5466])).
% 6.66/2.58  tff(c_5480, plain, (k2_zfmisc_1('#skF_4', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5467, c_2502])).
% 6.66/2.58  tff(c_5549, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5417, c_5480])).
% 6.66/2.58  tff(c_5554, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5549, c_112])).
% 6.66/2.58  tff(c_5560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5413, c_5554])).
% 6.66/2.58  tff(c_5561, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_5466])).
% 6.66/2.58  tff(c_5564, plain, (k2_zfmisc_1('#skF_1', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5561, c_2502])).
% 6.66/2.58  tff(c_5617, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5416, c_5564])).
% 6.66/2.58  tff(c_5662, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5617, c_112])).
% 6.66/2.58  tff(c_5668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5413, c_5662])).
% 6.66/2.58  tff(c_5669, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 6.66/2.58  tff(c_5771, plain, (![C_773, A_774, B_775]: (v1_relat_1(C_773) | ~m1_subset_1(C_773, k1_zfmisc_1(k2_zfmisc_1(A_774, B_775))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.66/2.58  tff(c_5792, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_5771])).
% 6.66/2.58  tff(c_5814, plain, (![C_777, B_778, A_779]: (v5_relat_1(C_777, B_778) | ~m1_subset_1(C_777, k1_zfmisc_1(k2_zfmisc_1(A_779, B_778))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.66/2.58  tff(c_5836, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_5814])).
% 6.66/2.58  tff(c_5919, plain, (![A_793, B_794, D_795]: (r2_relset_1(A_793, B_794, D_795, D_795) | ~m1_subset_1(D_795, k1_zfmisc_1(k2_zfmisc_1(A_793, B_794))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.66/2.58  tff(c_5933, plain, (![A_30]: (r2_relset_1(A_30, A_30, k6_partfun1(A_30), k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_46, c_5919])).
% 6.66/2.58  tff(c_5984, plain, (![A_804, B_805, C_806]: (k2_relset_1(A_804, B_805, C_806)=k2_relat_1(C_806) | ~m1_subset_1(C_806, k1_zfmisc_1(k2_zfmisc_1(A_804, B_805))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.66/2.58  tff(c_6006, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_5984])).
% 6.66/2.58  tff(c_6047, plain, (![D_810, C_811, A_812, B_813]: (D_810=C_811 | ~r2_relset_1(A_812, B_813, C_811, D_810) | ~m1_subset_1(D_810, k1_zfmisc_1(k2_zfmisc_1(A_812, B_813))) | ~m1_subset_1(C_811, k1_zfmisc_1(k2_zfmisc_1(A_812, B_813))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.66/2.58  tff(c_6053, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_6047])).
% 6.66/2.58  tff(c_6064, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6053])).
% 6.66/2.58  tff(c_6380, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_6064])).
% 6.66/2.58  tff(c_6487, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_6380])).
% 6.66/2.58  tff(c_6494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_6487])).
% 6.66/2.58  tff(c_6495, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_6064])).
% 6.66/2.58  tff(c_6670, plain, (![A_909, B_910, C_911, D_912]: (k2_relset_1(A_909, B_910, C_911)=B_910 | ~r2_relset_1(B_910, B_910, k1_partfun1(B_910, A_909, A_909, B_910, D_912, C_911), k6_partfun1(B_910)) | ~m1_subset_1(D_912, k1_zfmisc_1(k2_zfmisc_1(B_910, A_909))) | ~v1_funct_2(D_912, B_910, A_909) | ~v1_funct_1(D_912) | ~m1_subset_1(C_911, k1_zfmisc_1(k2_zfmisc_1(A_909, B_910))) | ~v1_funct_2(C_911, A_909, B_910) | ~v1_funct_1(C_911))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.66/2.58  tff(c_6673, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6495, c_6670])).
% 6.66/2.58  tff(c_6678, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_5933, c_6006, c_6673])).
% 6.66/2.58  tff(c_36, plain, (![B_23]: (v2_funct_2(B_23, k2_relat_1(B_23)) | ~v5_relat_1(B_23, k2_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.66/2.58  tff(c_6687, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6678, c_36])).
% 6.66/2.58  tff(c_6694, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5792, c_5836, c_6678, c_6687])).
% 6.66/2.58  tff(c_6696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5669, c_6694])).
% 6.66/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.58  
% 6.66/2.58  Inference rules
% 6.66/2.58  ----------------------
% 6.66/2.58  #Ref     : 0
% 6.66/2.58  #Sup     : 1476
% 6.66/2.58  #Fact    : 0
% 6.66/2.58  #Define  : 0
% 6.66/2.58  #Split   : 27
% 6.66/2.58  #Chain   : 0
% 6.66/2.58  #Close   : 0
% 6.66/2.58  
% 6.66/2.58  Ordering : KBO
% 6.66/2.58  
% 6.66/2.58  Simplification rules
% 6.66/2.58  ----------------------
% 6.66/2.58  #Subsume      : 123
% 6.66/2.58  #Demod        : 1232
% 6.66/2.58  #Tautology    : 716
% 6.66/2.58  #SimpNegUnit  : 7
% 6.66/2.58  #BackRed      : 206
% 6.66/2.58  
% 6.66/2.58  #Partial instantiations: 0
% 6.66/2.58  #Strategies tried      : 1
% 6.66/2.58  
% 6.66/2.58  Timing (in seconds)
% 6.66/2.58  ----------------------
% 6.66/2.58  Preprocessing        : 0.34
% 6.66/2.58  Parsing              : 0.19
% 6.66/2.58  CNF conversion       : 0.02
% 6.66/2.58  Main loop            : 1.43
% 6.66/2.58  Inferencing          : 0.51
% 6.66/2.58  Reduction            : 0.51
% 6.66/2.58  Demodulation         : 0.37
% 6.66/2.58  BG Simplification    : 0.05
% 6.66/2.58  Subsumption          : 0.24
% 6.66/2.58  Abstraction          : 0.05
% 6.66/2.58  MUC search           : 0.00
% 6.66/2.58  Cooper               : 0.00
% 6.66/2.58  Total                : 1.84
% 6.66/2.58  Index Insertion      : 0.00
% 6.66/2.59  Index Deletion       : 0.00
% 6.66/2.59  Index Matching       : 0.00
% 6.66/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
