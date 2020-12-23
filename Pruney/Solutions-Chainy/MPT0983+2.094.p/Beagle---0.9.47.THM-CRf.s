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
% DateTime   : Thu Dec  3 10:12:14 EST 2020

% Result     : Theorem 5.75s
% Output     : CNFRefutation 5.75s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 326 expanded)
%              Number of leaves         :   45 ( 138 expanded)
%              Depth                    :   10
%              Number of atoms          :  198 (1003 expanded)
%              Number of equality atoms :   38 ( 108 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k3_mcart_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(f_165,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_106,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_68,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_145,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_40,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_123,axiom,(
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

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_54,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_126,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_32,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_1'(A_21),A_21)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_46,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_16,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_70,plain,(
    ! [A_6] : v2_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16])).

tff(c_42,plain,(
    ! [C_39,B_38,A_37,D_40,F_42,E_41] :
      ( m1_subset_1(k1_partfun1(A_37,B_38,C_39,D_40,E_41,F_42),k1_zfmisc_1(k2_zfmisc_1(A_37,D_40)))
      | ~ m1_subset_1(F_42,k1_zfmisc_1(k2_zfmisc_1(C_39,D_40)))
      | ~ v1_funct_1(F_42)
      | ~ m1_subset_1(E_41,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38)))
      | ~ v1_funct_1(E_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    ! [A_20] : m1_subset_1(k6_relat_1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_69,plain,(
    ! [A_20] : m1_subset_1(k6_partfun1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_30])).

tff(c_56,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1112,plain,(
    ! [D_260,C_261,A_262,B_263] :
      ( D_260 = C_261
      | ~ r2_relset_1(A_262,B_263,C_261,D_260)
      | ~ m1_subset_1(D_260,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263)))
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1122,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_56,c_1112])).

tff(c_1141,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1122])).

tff(c_1572,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1141])).

tff(c_1575,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1572])).

tff(c_1579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_1575])).

tff(c_1580,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1141])).

tff(c_1601,plain,(
    ! [C_356,B_357,A_358,E_355,D_359] :
      ( k1_xboole_0 = C_356
      | v2_funct_1(D_359)
      | ~ v2_funct_1(k1_partfun1(A_358,B_357,B_357,C_356,D_359,E_355))
      | ~ m1_subset_1(E_355,k1_zfmisc_1(k2_zfmisc_1(B_357,C_356)))
      | ~ v1_funct_2(E_355,B_357,C_356)
      | ~ v1_funct_1(E_355)
      | ~ m1_subset_1(D_359,k1_zfmisc_1(k2_zfmisc_1(A_358,B_357)))
      | ~ v1_funct_2(D_359,A_358,B_357)
      | ~ v1_funct_1(D_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1603,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1580,c_1601])).

tff(c_1605,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_60,c_58,c_70,c_1603])).

tff(c_1606,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_1605])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1646,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1606,c_2])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1644,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1606,c_1606,c_8])).

tff(c_203,plain,(
    ! [C_73,B_74,A_75] :
      ( ~ v1_xboole_0(C_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(C_73))
      | ~ r2_hidden(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_217,plain,(
    ! [A_75] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_75,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_203])).

tff(c_232,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_1777,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1644,c_232])).

tff(c_1781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1646,c_1777])).

tff(c_1784,plain,(
    ! [A_376] : ~ r2_hidden(A_376,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_1789,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_1784])).

tff(c_102,plain,(
    ! [A_60] : k6_relat_1(A_60) = k6_partfun1(A_60) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_108,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_12])).

tff(c_121,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_70])).

tff(c_1816,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1789,c_121])).

tff(c_1824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_1816])).

tff(c_1825,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1844,plain,(
    ! [C_382,A_383,B_384] :
      ( v1_relat_1(C_382)
      | ~ m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(A_383,B_384))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1860,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1844])).

tff(c_1902,plain,(
    ! [C_392,B_393,A_394] :
      ( v5_relat_1(C_392,B_393)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(A_394,B_393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1919,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1902])).

tff(c_2028,plain,(
    ! [A_427,B_428,D_429] :
      ( r2_relset_1(A_427,B_428,D_429,D_429)
      | ~ m1_subset_1(D_429,k1_zfmisc_1(k2_zfmisc_1(A_427,B_428))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2039,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_69,c_2028])).

tff(c_2058,plain,(
    ! [A_434,B_435,C_436] :
      ( k2_relset_1(A_434,B_435,C_436) = k2_relat_1(C_436)
      | ~ m1_subset_1(C_436,k1_zfmisc_1(k2_zfmisc_1(A_434,B_435))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2075,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_2058])).

tff(c_2098,plain,(
    ! [D_438,C_439,A_440,B_441] :
      ( D_438 = C_439
      | ~ r2_relset_1(A_440,B_441,C_439,D_438)
      | ~ m1_subset_1(D_438,k1_zfmisc_1(k2_zfmisc_1(A_440,B_441)))
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(A_440,B_441))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2108,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_56,c_2098])).

tff(c_2127,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2108])).

tff(c_2353,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2127])).

tff(c_2356,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_2353])).

tff(c_2360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_2356])).

tff(c_2361,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2127])).

tff(c_2511,plain,(
    ! [A_548,B_549,C_550,D_551] :
      ( k2_relset_1(A_548,B_549,C_550) = B_549
      | ~ r2_relset_1(B_549,B_549,k1_partfun1(B_549,A_548,A_548,B_549,D_551,C_550),k6_partfun1(B_549))
      | ~ m1_subset_1(D_551,k1_zfmisc_1(k2_zfmisc_1(B_549,A_548)))
      | ~ v1_funct_2(D_551,B_549,A_548)
      | ~ v1_funct_1(D_551)
      | ~ m1_subset_1(C_550,k1_zfmisc_1(k2_zfmisc_1(A_548,B_549)))
      | ~ v1_funct_2(C_550,A_548,B_549)
      | ~ v1_funct_1(C_550) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2514,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2361,c_2511])).

tff(c_2519,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_68,c_66,c_64,c_2039,c_2075,c_2514])).

tff(c_38,plain,(
    ! [B_36] :
      ( v2_funct_2(B_36,k2_relat_1(B_36))
      | ~ v5_relat_1(B_36,k2_relat_1(B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2525,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2519,c_38])).

tff(c_2529,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1860,c_1919,c_2519,c_2525])).

tff(c_2531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1825,c_2529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:47:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.75/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.10  
% 5.75/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.10  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k3_mcart_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.75/2.10  
% 5.75/2.10  %Foreground sorts:
% 5.75/2.10  
% 5.75/2.10  
% 5.75/2.10  %Background operators:
% 5.75/2.10  
% 5.75/2.10  
% 5.75/2.10  %Foreground operators:
% 5.75/2.10  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.75/2.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.75/2.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.75/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.10  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.75/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.75/2.10  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.75/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.75/2.10  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.75/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.75/2.10  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.75/2.10  tff('#skF_5', type, '#skF_5': $i).
% 5.75/2.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.75/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.75/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.75/2.10  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.75/2.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.75/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.10  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.75/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.75/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.75/2.10  tff('#skF_4', type, '#skF_4': $i).
% 5.75/2.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.75/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.75/2.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.75/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.10  
% 5.75/2.12  tff(f_165, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.75/2.12  tff(f_84, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 5.75/2.12  tff(f_106, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.75/2.12  tff(f_44, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.75/2.12  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.75/2.12  tff(f_68, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.75/2.12  tff(f_66, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.75/2.12  tff(f_145, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 5.75/2.12  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.75/2.12  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.75/2.12  tff(f_39, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.75/2.12  tff(f_40, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 5.75/2.12  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.75/2.12  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.75/2.12  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.75/2.12  tff(f_123, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.75/2.12  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.75/2.12  tff(c_54, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.75/2.12  tff(c_126, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 5.75/2.12  tff(c_32, plain, (![A_21]: (r2_hidden('#skF_1'(A_21), A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.75/2.12  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.75/2.12  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.75/2.12  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.75/2.12  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.75/2.12  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.75/2.12  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.75/2.12  tff(c_46, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.75/2.12  tff(c_16, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.75/2.12  tff(c_70, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_16])).
% 5.75/2.12  tff(c_42, plain, (![C_39, B_38, A_37, D_40, F_42, E_41]: (m1_subset_1(k1_partfun1(A_37, B_38, C_39, D_40, E_41, F_42), k1_zfmisc_1(k2_zfmisc_1(A_37, D_40))) | ~m1_subset_1(F_42, k1_zfmisc_1(k2_zfmisc_1(C_39, D_40))) | ~v1_funct_1(F_42) | ~m1_subset_1(E_41, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))) | ~v1_funct_1(E_41))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.75/2.12  tff(c_30, plain, (![A_20]: (m1_subset_1(k6_relat_1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.75/2.12  tff(c_69, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_30])).
% 5.75/2.12  tff(c_56, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.75/2.12  tff(c_1112, plain, (![D_260, C_261, A_262, B_263]: (D_260=C_261 | ~r2_relset_1(A_262, B_263, C_261, D_260) | ~m1_subset_1(D_260, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.75/2.12  tff(c_1122, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_56, c_1112])).
% 5.75/2.12  tff(c_1141, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_1122])).
% 5.75/2.12  tff(c_1572, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1141])).
% 5.75/2.12  tff(c_1575, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_1572])).
% 5.75/2.12  tff(c_1579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_1575])).
% 5.75/2.12  tff(c_1580, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1141])).
% 5.75/2.12  tff(c_1601, plain, (![C_356, B_357, A_358, E_355, D_359]: (k1_xboole_0=C_356 | v2_funct_1(D_359) | ~v2_funct_1(k1_partfun1(A_358, B_357, B_357, C_356, D_359, E_355)) | ~m1_subset_1(E_355, k1_zfmisc_1(k2_zfmisc_1(B_357, C_356))) | ~v1_funct_2(E_355, B_357, C_356) | ~v1_funct_1(E_355) | ~m1_subset_1(D_359, k1_zfmisc_1(k2_zfmisc_1(A_358, B_357))) | ~v1_funct_2(D_359, A_358, B_357) | ~v1_funct_1(D_359))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.75/2.12  tff(c_1603, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1580, c_1601])).
% 5.75/2.12  tff(c_1605, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_60, c_58, c_70, c_1603])).
% 5.75/2.12  tff(c_1606, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_126, c_1605])).
% 5.75/2.12  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.75/2.12  tff(c_1646, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_2])).
% 5.75/2.12  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.75/2.12  tff(c_1644, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_1606, c_8])).
% 5.75/2.12  tff(c_203, plain, (![C_73, B_74, A_75]: (~v1_xboole_0(C_73) | ~m1_subset_1(B_74, k1_zfmisc_1(C_73)) | ~r2_hidden(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.75/2.12  tff(c_217, plain, (![A_75]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_75, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_203])).
% 5.75/2.12  tff(c_232, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_217])).
% 5.75/2.12  tff(c_1777, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1644, c_232])).
% 5.75/2.12  tff(c_1781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1646, c_1777])).
% 5.75/2.12  tff(c_1784, plain, (![A_376]: (~r2_hidden(A_376, '#skF_4'))), inference(splitRight, [status(thm)], [c_217])).
% 5.75/2.12  tff(c_1789, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_1784])).
% 5.75/2.12  tff(c_102, plain, (![A_60]: (k6_relat_1(A_60)=k6_partfun1(A_60))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.75/2.12  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.75/2.12  tff(c_108, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_102, c_12])).
% 5.75/2.12  tff(c_121, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_108, c_70])).
% 5.75/2.12  tff(c_1816, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1789, c_121])).
% 5.75/2.12  tff(c_1824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_1816])).
% 5.75/2.12  tff(c_1825, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 5.75/2.12  tff(c_1844, plain, (![C_382, A_383, B_384]: (v1_relat_1(C_382) | ~m1_subset_1(C_382, k1_zfmisc_1(k2_zfmisc_1(A_383, B_384))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.75/2.12  tff(c_1860, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_1844])).
% 5.75/2.12  tff(c_1902, plain, (![C_392, B_393, A_394]: (v5_relat_1(C_392, B_393) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1(A_394, B_393))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.75/2.12  tff(c_1919, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_1902])).
% 5.75/2.12  tff(c_2028, plain, (![A_427, B_428, D_429]: (r2_relset_1(A_427, B_428, D_429, D_429) | ~m1_subset_1(D_429, k1_zfmisc_1(k2_zfmisc_1(A_427, B_428))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.75/2.12  tff(c_2039, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_69, c_2028])).
% 5.75/2.12  tff(c_2058, plain, (![A_434, B_435, C_436]: (k2_relset_1(A_434, B_435, C_436)=k2_relat_1(C_436) | ~m1_subset_1(C_436, k1_zfmisc_1(k2_zfmisc_1(A_434, B_435))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.75/2.12  tff(c_2075, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_2058])).
% 5.75/2.12  tff(c_2098, plain, (![D_438, C_439, A_440, B_441]: (D_438=C_439 | ~r2_relset_1(A_440, B_441, C_439, D_438) | ~m1_subset_1(D_438, k1_zfmisc_1(k2_zfmisc_1(A_440, B_441))) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(A_440, B_441))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.75/2.12  tff(c_2108, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_56, c_2098])).
% 5.75/2.12  tff(c_2127, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_2108])).
% 5.75/2.12  tff(c_2353, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2127])).
% 5.75/2.12  tff(c_2356, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_2353])).
% 5.75/2.12  tff(c_2360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_2356])).
% 5.75/2.12  tff(c_2361, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2127])).
% 5.75/2.12  tff(c_2511, plain, (![A_548, B_549, C_550, D_551]: (k2_relset_1(A_548, B_549, C_550)=B_549 | ~r2_relset_1(B_549, B_549, k1_partfun1(B_549, A_548, A_548, B_549, D_551, C_550), k6_partfun1(B_549)) | ~m1_subset_1(D_551, k1_zfmisc_1(k2_zfmisc_1(B_549, A_548))) | ~v1_funct_2(D_551, B_549, A_548) | ~v1_funct_1(D_551) | ~m1_subset_1(C_550, k1_zfmisc_1(k2_zfmisc_1(A_548, B_549))) | ~v1_funct_2(C_550, A_548, B_549) | ~v1_funct_1(C_550))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.75/2.12  tff(c_2514, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2361, c_2511])).
% 5.75/2.12  tff(c_2519, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_68, c_66, c_64, c_2039, c_2075, c_2514])).
% 5.75/2.12  tff(c_38, plain, (![B_36]: (v2_funct_2(B_36, k2_relat_1(B_36)) | ~v5_relat_1(B_36, k2_relat_1(B_36)) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.75/2.12  tff(c_2525, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2519, c_38])).
% 5.75/2.12  tff(c_2529, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1860, c_1919, c_2519, c_2525])).
% 5.75/2.12  tff(c_2531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1825, c_2529])).
% 5.75/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.12  
% 5.75/2.12  Inference rules
% 5.75/2.12  ----------------------
% 5.75/2.12  #Ref     : 0
% 5.75/2.12  #Sup     : 531
% 5.75/2.12  #Fact    : 0
% 5.75/2.12  #Define  : 0
% 5.75/2.12  #Split   : 16
% 5.75/2.12  #Chain   : 0
% 5.75/2.12  #Close   : 0
% 5.75/2.12  
% 5.75/2.12  Ordering : KBO
% 5.75/2.12  
% 5.75/2.12  Simplification rules
% 5.75/2.12  ----------------------
% 5.75/2.12  #Subsume      : 55
% 5.75/2.12  #Demod        : 670
% 5.75/2.12  #Tautology    : 161
% 5.75/2.12  #SimpNegUnit  : 9
% 5.75/2.12  #BackRed      : 192
% 5.75/2.12  
% 5.75/2.12  #Partial instantiations: 0
% 5.75/2.12  #Strategies tried      : 1
% 5.75/2.12  
% 5.75/2.12  Timing (in seconds)
% 5.75/2.12  ----------------------
% 5.75/2.12  Preprocessing        : 0.37
% 5.75/2.12  Parsing              : 0.19
% 5.75/2.12  CNF conversion       : 0.03
% 5.75/2.12  Main loop            : 0.98
% 5.75/2.12  Inferencing          : 0.34
% 5.98/2.13  Reduction            : 0.34
% 5.98/2.13  Demodulation         : 0.25
% 5.98/2.13  BG Simplification    : 0.04
% 5.98/2.13  Subsumption          : 0.18
% 5.98/2.13  Abstraction          : 0.04
% 5.98/2.13  MUC search           : 0.00
% 5.98/2.13  Cooper               : 0.00
% 5.98/2.13  Total                : 1.39
% 5.98/2.13  Index Insertion      : 0.00
% 5.98/2.13  Index Deletion       : 0.00
% 5.98/2.13  Index Matching       : 0.00
% 5.98/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
