%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0986+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:12 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   44 (  54 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    5
%              Number of atoms          :   59 ( 117 expanded)
%              Number of equality atoms :   23 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(D)
            & r2_hidden(C,A) )
         => ( B = k1_xboole_0
            | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_35,plain,(
    ! [C_12,A_13,B_14] :
      ( v1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_39,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_35])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_41,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_relset_1(A_16,B_17,C_18) = k1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_45,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_41])).

tff(c_62,plain,(
    ! [B_27,A_28,C_29] :
      ( k1_xboole_0 = B_27
      | k1_relset_1(A_28,B_27,C_29) = A_28
      | ~ v1_funct_2(C_29,A_28,B_27)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_28,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_65,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_62])).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_45,c_65])).

tff(c_69,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_68])).

tff(c_79,plain,(
    ! [B_30,A_31] :
      ( k1_funct_1(k2_funct_1(B_30),k1_funct_1(B_30,A_31)) = A_31
      | ~ r2_hidden(A_31,k1_relat_1(B_30))
      | ~ v2_funct_1(B_30)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_88,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_22])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_34,c_28,c_26,c_69,c_88])).

%------------------------------------------------------------------------------
