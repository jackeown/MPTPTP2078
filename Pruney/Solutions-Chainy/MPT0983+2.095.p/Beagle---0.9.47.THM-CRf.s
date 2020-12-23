%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:14 EST 2020

% Result     : Theorem 5.15s
% Output     : CNFRefutation 5.15s
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
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k4_mcart_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_84,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_106,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_68,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_40,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

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
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_16,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_70,plain,(
    ! [A_6] : v2_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16])).

tff(c_42,plain,(
    ! [D_44,F_46,C_43,A_41,B_42,E_45] :
      ( m1_subset_1(k1_partfun1(A_41,B_42,C_43,D_44,E_45,F_46),k1_zfmisc_1(k2_zfmisc_1(A_41,D_44)))
      | ~ m1_subset_1(F_46,k1_zfmisc_1(k2_zfmisc_1(C_43,D_44)))
      | ~ v1_funct_1(F_46)
      | ~ m1_subset_1(E_45,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(E_45) ) ),
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

tff(c_1115,plain,(
    ! [D_267,C_268,A_269,B_270] :
      ( D_267 = C_268
      | ~ r2_relset_1(A_269,B_270,C_268,D_267)
      | ~ m1_subset_1(D_267,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270)))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1127,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_56,c_1115])).

tff(c_1150,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1127])).

tff(c_1572,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1150])).

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
    inference(splitRight,[status(thm)],[c_1150])).

tff(c_1601,plain,(
    ! [C_368,A_369,E_367,B_371,D_370] :
      ( k1_xboole_0 = C_368
      | v2_funct_1(D_370)
      | ~ v2_funct_1(k1_partfun1(A_369,B_371,B_371,C_368,D_370,E_367))
      | ~ m1_subset_1(E_367,k1_zfmisc_1(k2_zfmisc_1(B_371,C_368)))
      | ~ v1_funct_2(E_367,B_371,C_368)
      | ~ v1_funct_1(E_367)
      | ~ m1_subset_1(D_370,k1_zfmisc_1(k2_zfmisc_1(A_369,B_371)))
      | ~ v1_funct_2(D_370,A_369,B_371)
      | ~ v1_funct_1(D_370) ) ),
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
    ! [C_77,B_78,A_79] :
      ( ~ v1_xboole_0(C_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(C_77))
      | ~ r2_hidden(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_217,plain,(
    ! [A_79] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_79,'#skF_4') ) ),
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
    ! [A_388] : ~ r2_hidden(A_388,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_1789,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_1784])).

tff(c_102,plain,(
    ! [A_64] : k6_relat_1(A_64) = k6_partfun1(A_64) ),
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
    ! [C_394,A_395,B_396] :
      ( v1_relat_1(C_394)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(k2_zfmisc_1(A_395,B_396))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1860,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1844])).

tff(c_1902,plain,(
    ! [C_404,B_405,A_406] :
      ( v5_relat_1(C_404,B_405)
      | ~ m1_subset_1(C_404,k1_zfmisc_1(k2_zfmisc_1(A_406,B_405))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1919,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1902])).

tff(c_2002,plain,(
    ! [A_422,B_423,D_424] :
      ( r2_relset_1(A_422,B_423,D_424,D_424)
      | ~ m1_subset_1(D_424,k1_zfmisc_1(k2_zfmisc_1(A_422,B_423))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2013,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_69,c_2002])).

tff(c_2061,plain,(
    ! [A_445,B_446,C_447] :
      ( k2_relset_1(A_445,B_446,C_447) = k2_relat_1(C_447)
      | ~ m1_subset_1(C_447,k1_zfmisc_1(k2_zfmisc_1(A_445,B_446))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2078,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_2061])).

tff(c_2101,plain,(
    ! [D_449,C_450,A_451,B_452] :
      ( D_449 = C_450
      | ~ r2_relset_1(A_451,B_452,C_450,D_449)
      | ~ m1_subset_1(D_449,k1_zfmisc_1(k2_zfmisc_1(A_451,B_452)))
      | ~ m1_subset_1(C_450,k1_zfmisc_1(k2_zfmisc_1(A_451,B_452))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2113,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_56,c_2101])).

tff(c_2136,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2113])).

tff(c_2353,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2136])).

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
    inference(splitRight,[status(thm)],[c_2136])).

tff(c_2511,plain,(
    ! [A_564,B_565,C_566,D_567] :
      ( k2_relset_1(A_564,B_565,C_566) = B_565
      | ~ r2_relset_1(B_565,B_565,k1_partfun1(B_565,A_564,A_564,B_565,D_567,C_566),k6_partfun1(B_565))
      | ~ m1_subset_1(D_567,k1_zfmisc_1(k2_zfmisc_1(B_565,A_564)))
      | ~ v1_funct_2(D_567,B_565,A_564)
      | ~ v1_funct_1(D_567)
      | ~ m1_subset_1(C_566,k1_zfmisc_1(k2_zfmisc_1(A_564,B_565)))
      | ~ v1_funct_2(C_566,A_564,B_565)
      | ~ v1_funct_1(C_566) ) ),
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
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_68,c_66,c_64,c_2013,c_2078,c_2514])).

tff(c_38,plain,(
    ! [B_40] :
      ( v2_funct_2(B_40,k2_relat_1(B_40))
      | ~ v5_relat_1(B_40,k2_relat_1(B_40))
      | ~ v1_relat_1(B_40) ) ),
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
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.15/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/1.95  
% 5.15/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/1.95  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k4_mcart_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.15/1.95  
% 5.15/1.95  %Foreground sorts:
% 5.15/1.95  
% 5.15/1.95  
% 5.15/1.95  %Background operators:
% 5.15/1.95  
% 5.15/1.95  
% 5.15/1.95  %Foreground operators:
% 5.15/1.95  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.15/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.15/1.95  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.15/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.15/1.95  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.15/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.15/1.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.15/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.15/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.15/1.95  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.15/1.95  tff('#skF_5', type, '#skF_5': $i).
% 5.15/1.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.15/1.95  tff('#skF_2', type, '#skF_2': $i).
% 5.15/1.95  tff('#skF_3', type, '#skF_3': $i).
% 5.15/1.95  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.15/1.95  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.15/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.15/1.95  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.15/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.15/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.15/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.15/1.95  tff('#skF_4', type, '#skF_4': $i).
% 5.15/1.95  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.15/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.15/1.95  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.15/1.95  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 5.15/1.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.15/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.15/1.95  
% 5.15/1.97  tff(f_165, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.15/1.97  tff(f_84, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 5.15/1.97  tff(f_106, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.15/1.97  tff(f_44, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.15/1.97  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.15/1.97  tff(f_68, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.15/1.97  tff(f_66, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.15/1.97  tff(f_145, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 5.15/1.97  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.15/1.97  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.15/1.97  tff(f_39, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.15/1.97  tff(f_40, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 5.15/1.97  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.15/1.97  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.15/1.97  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.15/1.97  tff(f_123, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.15/1.97  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.15/1.97  tff(c_54, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.15/1.97  tff(c_126, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 5.15/1.97  tff(c_32, plain, (![A_21]: (r2_hidden('#skF_1'(A_21), A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.15/1.97  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.15/1.97  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.15/1.97  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.15/1.97  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.15/1.97  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.15/1.97  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.15/1.97  tff(c_46, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.15/1.97  tff(c_16, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.15/1.97  tff(c_70, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_16])).
% 5.15/1.97  tff(c_42, plain, (![D_44, F_46, C_43, A_41, B_42, E_45]: (m1_subset_1(k1_partfun1(A_41, B_42, C_43, D_44, E_45, F_46), k1_zfmisc_1(k2_zfmisc_1(A_41, D_44))) | ~m1_subset_1(F_46, k1_zfmisc_1(k2_zfmisc_1(C_43, D_44))) | ~v1_funct_1(F_46) | ~m1_subset_1(E_45, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(E_45))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.15/1.97  tff(c_30, plain, (![A_20]: (m1_subset_1(k6_relat_1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.15/1.97  tff(c_69, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_30])).
% 5.15/1.97  tff(c_56, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.15/1.97  tff(c_1115, plain, (![D_267, C_268, A_269, B_270]: (D_267=C_268 | ~r2_relset_1(A_269, B_270, C_268, D_267) | ~m1_subset_1(D_267, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.15/1.97  tff(c_1127, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_56, c_1115])).
% 5.15/1.97  tff(c_1150, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_1127])).
% 5.15/1.97  tff(c_1572, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1150])).
% 5.15/1.97  tff(c_1575, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_1572])).
% 5.15/1.97  tff(c_1579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_1575])).
% 5.15/1.97  tff(c_1580, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1150])).
% 5.15/1.97  tff(c_1601, plain, (![C_368, A_369, E_367, B_371, D_370]: (k1_xboole_0=C_368 | v2_funct_1(D_370) | ~v2_funct_1(k1_partfun1(A_369, B_371, B_371, C_368, D_370, E_367)) | ~m1_subset_1(E_367, k1_zfmisc_1(k2_zfmisc_1(B_371, C_368))) | ~v1_funct_2(E_367, B_371, C_368) | ~v1_funct_1(E_367) | ~m1_subset_1(D_370, k1_zfmisc_1(k2_zfmisc_1(A_369, B_371))) | ~v1_funct_2(D_370, A_369, B_371) | ~v1_funct_1(D_370))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.15/1.97  tff(c_1603, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1580, c_1601])).
% 5.15/1.97  tff(c_1605, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_60, c_58, c_70, c_1603])).
% 5.15/1.97  tff(c_1606, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_126, c_1605])).
% 5.15/1.97  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.15/1.97  tff(c_1646, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_2])).
% 5.15/1.97  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.15/1.97  tff(c_1644, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_1606, c_8])).
% 5.15/1.97  tff(c_203, plain, (![C_77, B_78, A_79]: (~v1_xboole_0(C_77) | ~m1_subset_1(B_78, k1_zfmisc_1(C_77)) | ~r2_hidden(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.15/1.97  tff(c_217, plain, (![A_79]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_79, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_203])).
% 5.15/1.97  tff(c_232, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_217])).
% 5.15/1.97  tff(c_1777, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1644, c_232])).
% 5.15/1.97  tff(c_1781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1646, c_1777])).
% 5.15/1.97  tff(c_1784, plain, (![A_388]: (~r2_hidden(A_388, '#skF_4'))), inference(splitRight, [status(thm)], [c_217])).
% 5.15/1.97  tff(c_1789, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_1784])).
% 5.15/1.97  tff(c_102, plain, (![A_64]: (k6_relat_1(A_64)=k6_partfun1(A_64))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.15/1.97  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.15/1.97  tff(c_108, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_102, c_12])).
% 5.15/1.97  tff(c_121, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_108, c_70])).
% 5.15/1.97  tff(c_1816, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1789, c_121])).
% 5.15/1.97  tff(c_1824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_1816])).
% 5.15/1.97  tff(c_1825, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 5.15/1.97  tff(c_1844, plain, (![C_394, A_395, B_396]: (v1_relat_1(C_394) | ~m1_subset_1(C_394, k1_zfmisc_1(k2_zfmisc_1(A_395, B_396))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.15/1.97  tff(c_1860, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_1844])).
% 5.15/1.97  tff(c_1902, plain, (![C_404, B_405, A_406]: (v5_relat_1(C_404, B_405) | ~m1_subset_1(C_404, k1_zfmisc_1(k2_zfmisc_1(A_406, B_405))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.15/1.97  tff(c_1919, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_1902])).
% 5.15/1.97  tff(c_2002, plain, (![A_422, B_423, D_424]: (r2_relset_1(A_422, B_423, D_424, D_424) | ~m1_subset_1(D_424, k1_zfmisc_1(k2_zfmisc_1(A_422, B_423))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.15/1.97  tff(c_2013, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_69, c_2002])).
% 5.15/1.97  tff(c_2061, plain, (![A_445, B_446, C_447]: (k2_relset_1(A_445, B_446, C_447)=k2_relat_1(C_447) | ~m1_subset_1(C_447, k1_zfmisc_1(k2_zfmisc_1(A_445, B_446))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.15/1.97  tff(c_2078, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_2061])).
% 5.15/1.97  tff(c_2101, plain, (![D_449, C_450, A_451, B_452]: (D_449=C_450 | ~r2_relset_1(A_451, B_452, C_450, D_449) | ~m1_subset_1(D_449, k1_zfmisc_1(k2_zfmisc_1(A_451, B_452))) | ~m1_subset_1(C_450, k1_zfmisc_1(k2_zfmisc_1(A_451, B_452))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.15/1.97  tff(c_2113, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_56, c_2101])).
% 5.15/1.97  tff(c_2136, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_2113])).
% 5.15/1.97  tff(c_2353, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2136])).
% 5.15/1.97  tff(c_2356, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_2353])).
% 5.15/1.97  tff(c_2360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_2356])).
% 5.15/1.97  tff(c_2361, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2136])).
% 5.15/1.97  tff(c_2511, plain, (![A_564, B_565, C_566, D_567]: (k2_relset_1(A_564, B_565, C_566)=B_565 | ~r2_relset_1(B_565, B_565, k1_partfun1(B_565, A_564, A_564, B_565, D_567, C_566), k6_partfun1(B_565)) | ~m1_subset_1(D_567, k1_zfmisc_1(k2_zfmisc_1(B_565, A_564))) | ~v1_funct_2(D_567, B_565, A_564) | ~v1_funct_1(D_567) | ~m1_subset_1(C_566, k1_zfmisc_1(k2_zfmisc_1(A_564, B_565))) | ~v1_funct_2(C_566, A_564, B_565) | ~v1_funct_1(C_566))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.15/1.97  tff(c_2514, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2361, c_2511])).
% 5.15/1.97  tff(c_2519, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_68, c_66, c_64, c_2013, c_2078, c_2514])).
% 5.15/1.97  tff(c_38, plain, (![B_40]: (v2_funct_2(B_40, k2_relat_1(B_40)) | ~v5_relat_1(B_40, k2_relat_1(B_40)) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.15/1.97  tff(c_2525, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2519, c_38])).
% 5.15/1.97  tff(c_2529, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1860, c_1919, c_2519, c_2525])).
% 5.15/1.97  tff(c_2531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1825, c_2529])).
% 5.15/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/1.97  
% 5.15/1.97  Inference rules
% 5.15/1.97  ----------------------
% 5.15/1.97  #Ref     : 0
% 5.15/1.97  #Sup     : 531
% 5.15/1.97  #Fact    : 0
% 5.15/1.97  #Define  : 0
% 5.15/1.97  #Split   : 16
% 5.15/1.97  #Chain   : 0
% 5.15/1.97  #Close   : 0
% 5.15/1.97  
% 5.15/1.97  Ordering : KBO
% 5.15/1.97  
% 5.15/1.97  Simplification rules
% 5.15/1.97  ----------------------
% 5.15/1.97  #Subsume      : 55
% 5.15/1.97  #Demod        : 670
% 5.15/1.97  #Tautology    : 161
% 5.15/1.97  #SimpNegUnit  : 9
% 5.15/1.97  #BackRed      : 192
% 5.15/1.97  
% 5.15/1.97  #Partial instantiations: 0
% 5.15/1.97  #Strategies tried      : 1
% 5.15/1.97  
% 5.15/1.97  Timing (in seconds)
% 5.15/1.97  ----------------------
% 5.15/1.97  Preprocessing        : 0.35
% 5.15/1.97  Parsing              : 0.19
% 5.15/1.97  CNF conversion       : 0.02
% 5.15/1.97  Main loop            : 0.84
% 5.15/1.97  Inferencing          : 0.29
% 5.15/1.97  Reduction            : 0.30
% 5.15/1.97  Demodulation         : 0.22
% 5.15/1.97  BG Simplification    : 0.03
% 5.15/1.97  Subsumption          : 0.14
% 5.15/1.97  Abstraction          : 0.03
% 5.15/1.97  MUC search           : 0.00
% 5.15/1.97  Cooper               : 0.00
% 5.15/1.97  Total                : 1.23
% 5.15/1.97  Index Insertion      : 0.00
% 5.15/1.97  Index Deletion       : 0.00
% 5.15/1.97  Index Matching       : 0.00
% 5.15/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
