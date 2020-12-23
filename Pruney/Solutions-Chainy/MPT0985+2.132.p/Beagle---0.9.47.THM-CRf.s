%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:47 EST 2020

% Result     : Theorem 11.65s
% Output     : CNFRefutation 12.46s
% Verified   : 
% Statistics : Number of formulae       :  579 (13855 expanded)
%              Number of leaves         :   40 (4735 expanded)
%              Depth                    :   25
%              Number of atoms          : 1225 (45271 expanded)
%              Number of equality atoms :  369 (13934 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_150,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_108,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_108])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_8,plain,(
    ! [A_4] :
      ( v1_funct_1(k2_funct_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_77,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_80,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_77])).

tff(c_83,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_80])).

tff(c_93,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_100,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_93])).

tff(c_105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_100])).

tff(c_106,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_185,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_117,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_126,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_117])).

tff(c_62,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_227,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_237,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_227])).

tff(c_241,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_237])).

tff(c_18,plain,(
    ! [A_9] :
      ( k1_relat_1(k2_funct_1(A_9)) = k2_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_4] :
      ( v1_relat_1(k2_funct_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_107,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_151,plain,(
    ! [A_55] :
      ( k1_relat_1(k2_funct_1(A_55)) = k2_relat_1(A_55)
      | ~ v2_funct_1(A_55)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_48,plain,(
    ! [A_32] :
      ( v1_funct_2(A_32,k1_relat_1(A_32),k2_relat_1(A_32))
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_27085,plain,(
    ! [A_1674] :
      ( v1_funct_2(k2_funct_1(A_1674),k2_relat_1(A_1674),k2_relat_1(k2_funct_1(A_1674)))
      | ~ v1_funct_1(k2_funct_1(A_1674))
      | ~ v1_relat_1(k2_funct_1(A_1674))
      | ~ v2_funct_1(A_1674)
      | ~ v1_funct_1(A_1674)
      | ~ v1_relat_1(A_1674) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_48])).

tff(c_27091,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_27085])).

tff(c_27101,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_107,c_27091])).

tff(c_27102,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_27101])).

tff(c_27105,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_27102])).

tff(c_27109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_27105])).

tff(c_27111,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_27101])).

tff(c_171,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_180,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_171])).

tff(c_23064,plain,(
    ! [B_1425,A_1426,C_1427] :
      ( k1_xboole_0 = B_1425
      | k1_relset_1(A_1426,B_1425,C_1427) = A_1426
      | ~ v1_funct_2(C_1427,A_1426,B_1425)
      | ~ m1_subset_1(C_1427,k1_zfmisc_1(k2_zfmisc_1(A_1426,B_1425))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_23096,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_23064])).

tff(c_23111,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_180,c_23096])).

tff(c_23112,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_23111])).

tff(c_16,plain,(
    ! [A_9] :
      ( k2_relat_1(k2_funct_1(A_9)) = k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,(
    ! [A_32] :
      ( m1_subset_1(A_32,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_32),k2_relat_1(A_32))))
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_238,plain,(
    ! [A_32] :
      ( k2_relset_1(k1_relat_1(A_32),k2_relat_1(A_32),A_32) = k2_relat_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(resolution,[status(thm)],[c_46,c_227])).

tff(c_416,plain,(
    ! [A_80,B_81,C_82] :
      ( m1_subset_1(k2_relset_1(A_80,B_81,C_82),k1_zfmisc_1(B_81))
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26768,plain,(
    ! [A_1666] :
      ( m1_subset_1(k2_relat_1(A_1666),k1_zfmisc_1(k2_relat_1(A_1666)))
      | ~ m1_subset_1(A_1666,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1666),k2_relat_1(A_1666))))
      | ~ v1_funct_1(A_1666)
      | ~ v1_relat_1(A_1666) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_416])).

tff(c_26818,plain,(
    ! [A_1667] :
      ( m1_subset_1(k2_relat_1(A_1667),k1_zfmisc_1(k2_relat_1(A_1667)))
      | ~ v1_funct_1(A_1667)
      | ~ v1_relat_1(A_1667) ) ),
    inference(resolution,[status(thm)],[c_46,c_26768])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(A_2,B_3)
      | ~ m1_subset_1(A_2,k1_zfmisc_1(B_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26849,plain,(
    ! [A_1668] :
      ( r1_tarski(k2_relat_1(A_1668),k2_relat_1(A_1668))
      | ~ v1_funct_1(A_1668)
      | ~ v1_relat_1(A_1668) ) ),
    inference(resolution,[status(thm)],[c_26818,c_4])).

tff(c_27117,plain,(
    ! [A_1675] :
      ( r1_tarski(k2_relat_1(k2_funct_1(A_1675)),k1_relat_1(A_1675))
      | ~ v1_funct_1(k2_funct_1(A_1675))
      | ~ v1_relat_1(k2_funct_1(A_1675))
      | ~ v2_funct_1(A_1675)
      | ~ v1_funct_1(A_1675)
      | ~ v1_relat_1(A_1675) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_26849])).

tff(c_27130,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23112,c_27117])).

tff(c_27143,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_27111,c_107,c_27130])).

tff(c_52,plain,(
    ! [B_34,A_33] :
      ( m1_subset_1(B_34,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_34),A_33)))
      | ~ r1_tarski(k2_relat_1(B_34),A_33)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_22882,plain,(
    ! [B_1413,A_1414] :
      ( m1_subset_1(B_1413,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1413),A_1414)))
      | ~ r1_tarski(k2_relat_1(B_1413),A_1414)
      | ~ v1_funct_1(B_1413)
      | ~ v1_relat_1(B_1413) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_26,plain,(
    ! [A_19,B_20,C_21] :
      ( k2_relset_1(A_19,B_20,C_21) = k2_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22912,plain,(
    ! [B_1413,A_1414] :
      ( k2_relset_1(k1_relat_1(B_1413),A_1414,B_1413) = k2_relat_1(B_1413)
      | ~ r1_tarski(k2_relat_1(B_1413),A_1414)
      | ~ v1_funct_1(B_1413)
      | ~ v1_relat_1(B_1413) ) ),
    inference(resolution,[status(thm)],[c_22882,c_26])).

tff(c_27149,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_27143,c_22912])).

tff(c_27163,plain,(
    k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27111,c_107,c_27149])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k2_relset_1(A_13,B_14,C_15),k1_zfmisc_1(B_14))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_27178,plain,
    ( m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_27163,c_22])).

tff(c_27268,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_27178])).

tff(c_27349,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_27268])).

tff(c_27359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27111,c_107,c_27143,c_27349])).

tff(c_27361,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_27178])).

tff(c_27421,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_27361])).

tff(c_27444,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_241,c_27421])).

tff(c_27446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_27444])).

tff(c_27447,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_23111])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_513,plain,(
    ! [C_89,A_90] :
      ( k1_xboole_0 = C_89
      | ~ v1_funct_2(C_89,A_90,k1_xboole_0)
      | k1_xboole_0 = A_90
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_528,plain,(
    ! [A_2,A_90] :
      ( k1_xboole_0 = A_2
      | ~ v1_funct_2(A_2,A_90,k1_xboole_0)
      | k1_xboole_0 = A_90
      | ~ r1_tarski(A_2,k2_zfmisc_1(A_90,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_6,c_513])).

tff(c_27935,plain,(
    ! [A_1711,A_1712] :
      ( A_1711 = '#skF_2'
      | ~ v1_funct_2(A_1711,A_1712,'#skF_2')
      | A_1712 = '#skF_2'
      | ~ r1_tarski(A_1711,k2_zfmisc_1(A_1712,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27447,c_27447,c_27447,c_27447,c_528])).

tff(c_27961,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_116,c_27935])).

tff(c_27974,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_27961])).

tff(c_27975,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_27974])).

tff(c_19083,plain,(
    ! [A_1211] :
      ( v1_funct_2(k2_funct_1(A_1211),k2_relat_1(A_1211),k2_relat_1(k2_funct_1(A_1211)))
      | ~ v1_funct_1(k2_funct_1(A_1211))
      | ~ v1_relat_1(k2_funct_1(A_1211))
      | ~ v2_funct_1(A_1211)
      | ~ v1_funct_1(A_1211)
      | ~ v1_relat_1(A_1211) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_48])).

tff(c_19089,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_19083])).

tff(c_19099,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_107,c_19089])).

tff(c_19100,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_19099])).

tff(c_19103,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_19100])).

tff(c_19107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_19103])).

tff(c_19109,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_19099])).

tff(c_16066,plain,(
    ! [B_1025,A_1026,C_1027] :
      ( k1_xboole_0 = B_1025
      | k1_relset_1(A_1026,B_1025,C_1027) = A_1026
      | ~ v1_funct_2(C_1027,A_1026,B_1025)
      | ~ m1_subset_1(C_1027,k1_zfmisc_1(k2_zfmisc_1(A_1026,B_1025))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_16090,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_16066])).

tff(c_16102,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_180,c_16090])).

tff(c_16103,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_16102])).

tff(c_18794,plain,(
    ! [A_1199] :
      ( m1_subset_1(k2_relat_1(A_1199),k1_zfmisc_1(k2_relat_1(A_1199)))
      | ~ m1_subset_1(A_1199,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1199),k2_relat_1(A_1199))))
      | ~ v1_funct_1(A_1199)
      | ~ v1_relat_1(A_1199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_416])).

tff(c_18842,plain,(
    ! [A_1200] :
      ( m1_subset_1(k2_relat_1(A_1200),k1_zfmisc_1(k2_relat_1(A_1200)))
      | ~ v1_funct_1(A_1200)
      | ~ v1_relat_1(A_1200) ) ),
    inference(resolution,[status(thm)],[c_46,c_18794])).

tff(c_18873,plain,(
    ! [A_1201] :
      ( r1_tarski(k2_relat_1(A_1201),k2_relat_1(A_1201))
      | ~ v1_funct_1(A_1201)
      | ~ v1_relat_1(A_1201) ) ),
    inference(resolution,[status(thm)],[c_18842,c_4])).

tff(c_19115,plain,(
    ! [A_1212] :
      ( r1_tarski(k2_relat_1(k2_funct_1(A_1212)),k1_relat_1(A_1212))
      | ~ v1_funct_1(k2_funct_1(A_1212))
      | ~ v1_relat_1(k2_funct_1(A_1212))
      | ~ v2_funct_1(A_1212)
      | ~ v1_funct_1(A_1212)
      | ~ v1_relat_1(A_1212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_18873])).

tff(c_19128,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16103,c_19115])).

tff(c_19144,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_19109,c_107,c_19128])).

tff(c_15971,plain,(
    ! [B_1012,A_1013] :
      ( m1_subset_1(B_1012,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1012),A_1013)))
      | ~ r1_tarski(k2_relat_1(B_1012),A_1013)
      | ~ v1_funct_1(B_1012)
      | ~ v1_relat_1(B_1012) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_16004,plain,(
    ! [B_1012,A_1013] :
      ( k2_relset_1(k1_relat_1(B_1012),A_1013,B_1012) = k2_relat_1(B_1012)
      | ~ r1_tarski(k2_relat_1(B_1012),A_1013)
      | ~ v1_funct_1(B_1012)
      | ~ v1_relat_1(B_1012) ) ),
    inference(resolution,[status(thm)],[c_15971,c_26])).

tff(c_19154,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_19144,c_16004])).

tff(c_19169,plain,(
    k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19109,c_107,c_19154])).

tff(c_19216,plain,
    ( m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_19169,c_22])).

tff(c_19276,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_19216])).

tff(c_19355,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_19276])).

tff(c_19365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19109,c_107,c_19144,c_19355])).

tff(c_19367,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_19216])).

tff(c_19420,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_19367])).

tff(c_19443,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_241,c_19420])).

tff(c_19445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_19443])).

tff(c_19446,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16102])).

tff(c_20369,plain,(
    ! [A_1268,A_1269] :
      ( A_1268 = '#skF_2'
      | ~ v1_funct_2(A_1268,A_1269,'#skF_2')
      | A_1269 = '#skF_2'
      | ~ r1_tarski(A_1268,k2_zfmisc_1(A_1269,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19446,c_19446,c_19446,c_19446,c_528])).

tff(c_20383,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_116,c_20369])).

tff(c_20391,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_20383])).

tff(c_20392,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_20391])).

tff(c_9556,plain,(
    ! [B_652,A_653,C_654] :
      ( k1_xboole_0 = B_652
      | k1_relset_1(A_653,B_652,C_654) = A_653
      | ~ v1_funct_2(C_654,A_653,B_652)
      | ~ m1_subset_1(C_654,k1_zfmisc_1(k2_zfmisc_1(A_653,B_652))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_9580,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_9556])).

tff(c_9592,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_180,c_9580])).

tff(c_9593,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9592])).

tff(c_12174,plain,(
    ! [A_824] :
      ( m1_subset_1(k2_relat_1(A_824),k1_zfmisc_1(k2_relat_1(A_824)))
      | ~ m1_subset_1(A_824,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_824),k2_relat_1(A_824))))
      | ~ v1_funct_1(A_824)
      | ~ v1_relat_1(A_824) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_416])).

tff(c_12236,plain,(
    ! [A_827] :
      ( m1_subset_1(k2_relat_1(A_827),k1_zfmisc_1(k2_relat_1(A_827)))
      | ~ v1_funct_1(A_827)
      | ~ v1_relat_1(A_827) ) ),
    inference(resolution,[status(thm)],[c_46,c_12174])).

tff(c_12267,plain,(
    ! [A_828] :
      ( r1_tarski(k2_relat_1(A_828),k2_relat_1(A_828))
      | ~ v1_funct_1(A_828)
      | ~ v1_relat_1(A_828) ) ),
    inference(resolution,[status(thm)],[c_12236,c_4])).

tff(c_12383,plain,(
    ! [A_835] :
      ( r1_tarski(k2_relat_1(k2_funct_1(A_835)),k1_relat_1(A_835))
      | ~ v1_funct_1(k2_funct_1(A_835))
      | ~ v1_relat_1(k2_funct_1(A_835))
      | ~ v2_funct_1(A_835)
      | ~ v1_funct_1(A_835)
      | ~ v1_relat_1(A_835) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_12267])).

tff(c_12396,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9593,c_12383])).

tff(c_12409,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_107,c_12396])).

tff(c_12410,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_12409])).

tff(c_12425,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_12410])).

tff(c_12429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_12425])).

tff(c_12431,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_12409])).

tff(c_12430,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_12409])).

tff(c_9498,plain,(
    ! [B_645,A_646] :
      ( m1_subset_1(B_645,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_645),A_646)))
      | ~ r1_tarski(k2_relat_1(B_645),A_646)
      | ~ v1_funct_1(B_645)
      | ~ v1_relat_1(B_645) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_9528,plain,(
    ! [B_645,A_646] :
      ( k2_relset_1(k1_relat_1(B_645),A_646,B_645) = k2_relat_1(B_645)
      | ~ r1_tarski(k2_relat_1(B_645),A_646)
      | ~ v1_funct_1(B_645)
      | ~ v1_relat_1(B_645) ) ),
    inference(resolution,[status(thm)],[c_9498,c_26])).

tff(c_12437,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12430,c_9528])).

tff(c_12451,plain,(
    k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12431,c_107,c_12437])).

tff(c_12475,plain,
    ( m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12451,c_22])).

tff(c_12571,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_12475])).

tff(c_12574,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_12571])).

tff(c_12584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12431,c_107,c_12430,c_12574])).

tff(c_12586,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_12475])).

tff(c_12647,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_12586])).

tff(c_12670,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_241,c_12647])).

tff(c_12672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_12670])).

tff(c_12673,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_9592])).

tff(c_13390,plain,(
    ! [A_884,A_885] :
      ( A_884 = '#skF_2'
      | ~ v1_funct_2(A_884,A_885,'#skF_2')
      | A_885 = '#skF_2'
      | ~ r1_tarski(A_884,k2_zfmisc_1(A_885,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12673,c_12673,c_12673,c_12673,c_528])).

tff(c_13404,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_116,c_13390])).

tff(c_13413,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_13404])).

tff(c_13414,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_13413])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_190,plain,(
    ! [A_61,B_62,A_63] :
      ( k1_relset_1(A_61,B_62,A_63) = k1_relat_1(A_63)
      | ~ r1_tarski(A_63,k2_zfmisc_1(A_61,B_62)) ) ),
    inference(resolution,[status(thm)],[c_6,c_171])).

tff(c_200,plain,(
    ! [A_61,B_62] : k1_relset_1(A_61,B_62,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_190])).

tff(c_292,plain,(
    ! [A_70,B_71,A_72] :
      ( k2_relset_1(A_70,B_71,A_72) = k2_relat_1(A_72)
      | ~ r1_tarski(A_72,k2_zfmisc_1(A_70,B_71)) ) ),
    inference(resolution,[status(thm)],[c_6,c_227])).

tff(c_307,plain,(
    ! [A_70,B_71] : k2_relset_1(A_70,B_71,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_292])).

tff(c_457,plain,(
    ! [B_83,A_84] :
      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(B_83))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_416])).

tff(c_463,plain,(
    ! [B_83,A_84] :
      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(B_83))
      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(A_84,B_83)) ) ),
    inference(resolution,[status(thm)],[c_6,c_457])).

tff(c_469,plain,(
    ! [B_83] : m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(B_83)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_463])).

tff(c_526,plain,(
    ! [A_90] :
      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_2(k2_relat_1(k1_xboole_0),A_90,k1_xboole_0)
      | k1_xboole_0 = A_90 ) ),
    inference(resolution,[status(thm)],[c_469,c_513])).

tff(c_673,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_526])).

tff(c_682,plain,(
    ! [B_83] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(B_83)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_469])).

tff(c_753,plain,(
    ! [B_107,C_108] :
      ( k1_relset_1(k1_xboole_0,B_107,C_108) = k1_xboole_0
      | ~ v1_funct_2(C_108,k1_xboole_0,B_107)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_757,plain,(
    ! [B_107] :
      ( k1_relset_1(k1_xboole_0,B_107,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_107) ) ),
    inference(resolution,[status(thm)],[c_682,c_753])).

tff(c_767,plain,(
    ! [B_107] :
      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_757])).

tff(c_9414,plain,(
    ! [B_107] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_107) ),
    inference(splitLeft,[status(thm)],[c_767])).

tff(c_12680,plain,(
    ! [B_107] : ~ v1_funct_2('#skF_2','#skF_2',B_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12673,c_12673,c_9414])).

tff(c_13428,plain,(
    ! [B_107] : ~ v1_funct_2('#skF_1','#skF_1',B_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13414,c_13414,c_12680])).

tff(c_12674,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9592])).

tff(c_248,plain,
    ( v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_48])).

tff(c_254,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_248])).

tff(c_245,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_46])).

tff(c_252,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_245])).

tff(c_273,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_252,c_4])).

tff(c_13401,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_273,c_13390])).

tff(c_13410,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_13401])).

tff(c_13698,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13414,c_13414,c_13410])).

tff(c_13699,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_12674,c_13698])).

tff(c_13455,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13414,c_66])).

tff(c_13708,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13699,c_13455])).

tff(c_13720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13428,c_13708])).

tff(c_13721,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_13413])).

tff(c_796,plain,(
    ! [C_111,B_112] :
      ( v1_funct_2(C_111,k1_xboole_0,B_112)
      | k1_relset_1(k1_xboole_0,B_112,C_111) != k1_xboole_0
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_800,plain,(
    ! [B_112] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_112)
      | k1_relset_1(k1_xboole_0,B_112,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_682,c_796])).

tff(c_810,plain,(
    ! [B_112] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_112)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_800])).

tff(c_9466,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_9414,c_810])).

tff(c_12679,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12673,c_12673,c_9466])).

tff(c_13738,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13721,c_13721,c_12679])).

tff(c_13035,plain,(
    ! [A_872,A_873] :
      ( A_872 = '#skF_2'
      | ~ v1_funct_2(A_872,A_873,'#skF_2')
      | A_873 = '#skF_2'
      | ~ r1_tarski(A_872,k2_zfmisc_1(A_873,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12673,c_12673,c_12673,c_12673,c_528])).

tff(c_13049,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_116,c_13035])).

tff(c_13058,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_13049])).

tff(c_13059,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_13058])).

tff(c_13099,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13059,c_66])).

tff(c_13096,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13059,c_116])).

tff(c_13080,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13059,c_12673])).

tff(c_769,plain,(
    ! [B_107,A_2] :
      ( k1_relset_1(k1_xboole_0,B_107,A_2) = k1_xboole_0
      | ~ v1_funct_2(A_2,k1_xboole_0,B_107)
      | ~ r1_tarski(A_2,k2_zfmisc_1(k1_xboole_0,B_107)) ) ),
    inference(resolution,[status(thm)],[c_6,c_753])).

tff(c_13279,plain,(
    ! [B_882,A_883] :
      ( k1_relset_1('#skF_1',B_882,A_883) = '#skF_1'
      | ~ v1_funct_2(A_883,'#skF_1',B_882)
      | ~ r1_tarski(A_883,k2_zfmisc_1('#skF_1',B_882)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13080,c_13080,c_13080,c_13080,c_769])).

tff(c_13282,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_13096,c_13279])).

tff(c_13293,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13099,c_13282])).

tff(c_13097,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13059,c_64])).

tff(c_24,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_relset_1(A_16,B_17,C_18) = k1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_13318,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_13097,c_24])).

tff(c_13335,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13293,c_13318])).

tff(c_13337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12674,c_13335])).

tff(c_13338,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_13058])).

tff(c_127,plain,(
    ! [A_50,A_51,B_52] :
      ( v1_relat_1(A_50)
      | ~ r1_tarski(A_50,k2_zfmisc_1(A_51,B_52)) ) ),
    inference(resolution,[status(thm)],[c_6,c_117])).

tff(c_137,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_127])).

tff(c_12691,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12673,c_137])).

tff(c_5466,plain,(
    ! [B_409,A_410,C_411] :
      ( k1_xboole_0 = B_409
      | k1_relset_1(A_410,B_409,C_411) = A_410
      | ~ v1_funct_2(C_411,A_410,B_409)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(A_410,B_409))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_5490,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_5466])).

tff(c_5502,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_180,c_5490])).

tff(c_5503,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5502])).

tff(c_8029,plain,(
    ! [A_565] :
      ( m1_subset_1(k2_relat_1(A_565),k1_zfmisc_1(k2_relat_1(A_565)))
      | ~ m1_subset_1(A_565,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_565),k2_relat_1(A_565))))
      | ~ v1_funct_1(A_565)
      | ~ v1_relat_1(A_565) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_416])).

tff(c_8077,plain,(
    ! [A_566] :
      ( m1_subset_1(k2_relat_1(A_566),k1_zfmisc_1(k2_relat_1(A_566)))
      | ~ v1_funct_1(A_566)
      | ~ v1_relat_1(A_566) ) ),
    inference(resolution,[status(thm)],[c_46,c_8029])).

tff(c_8108,plain,(
    ! [A_567] :
      ( r1_tarski(k2_relat_1(A_567),k2_relat_1(A_567))
      | ~ v1_funct_1(A_567)
      | ~ v1_relat_1(A_567) ) ),
    inference(resolution,[status(thm)],[c_8077,c_4])).

tff(c_8249,plain,(
    ! [A_576] :
      ( r1_tarski(k2_relat_1(k2_funct_1(A_576)),k1_relat_1(A_576))
      | ~ v1_funct_1(k2_funct_1(A_576))
      | ~ v1_relat_1(k2_funct_1(A_576))
      | ~ v2_funct_1(A_576)
      | ~ v1_funct_1(A_576)
      | ~ v1_relat_1(A_576) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_8108])).

tff(c_8262,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5503,c_8249])).

tff(c_8278,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_107,c_8262])).

tff(c_8298,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8278])).

tff(c_8301,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_8298])).

tff(c_8305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_8301])).

tff(c_8307,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_8278])).

tff(c_8306,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_8278])).

tff(c_5344,plain,(
    ! [B_399,A_400] :
      ( m1_subset_1(B_399,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_399),A_400)))
      | ~ r1_tarski(k2_relat_1(B_399),A_400)
      | ~ v1_funct_1(B_399)
      | ~ v1_relat_1(B_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_5377,plain,(
    ! [B_399,A_400] :
      ( k2_relset_1(k1_relat_1(B_399),A_400,B_399) = k2_relat_1(B_399)
      | ~ r1_tarski(k2_relat_1(B_399),A_400)
      | ~ v1_funct_1(B_399)
      | ~ v1_relat_1(B_399) ) ),
    inference(resolution,[status(thm)],[c_5344,c_26])).

tff(c_8320,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8306,c_5377])).

tff(c_8334,plain,(
    k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8307,c_107,c_8320])).

tff(c_8362,plain,
    ( m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8334,c_22])).

tff(c_8449,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_8362])).

tff(c_8452,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_8449])).

tff(c_8462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8307,c_107,c_8306,c_8452])).

tff(c_8464,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_8362])).

tff(c_8584,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_8464])).

tff(c_8607,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_241,c_8584])).

tff(c_8609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_8607])).

tff(c_8610,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5502])).

tff(c_8979,plain,(
    ! [A_617,A_618] :
      ( A_617 = '#skF_2'
      | ~ v1_funct_2(A_617,A_618,'#skF_2')
      | A_618 = '#skF_2'
      | ~ r1_tarski(A_617,k2_zfmisc_1(A_618,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8610,c_8610,c_8610,c_8610,c_528])).

tff(c_8993,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_116,c_8979])).

tff(c_9001,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8993])).

tff(c_9002,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9001])).

tff(c_189,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_185])).

tff(c_982,plain,(
    ! [B_135,A_136,C_137] :
      ( k1_xboole_0 = B_135
      | k1_relset_1(A_136,B_135,C_137) = A_136
      | ~ v1_funct_2(C_137,A_136,B_135)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_136,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1006,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_982])).

tff(c_1018,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_180,c_1006])).

tff(c_1019,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1018])).

tff(c_3614,plain,(
    ! [A_306] :
      ( m1_subset_1(k2_relat_1(A_306),k1_zfmisc_1(k2_relat_1(A_306)))
      | ~ m1_subset_1(A_306,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_306),k2_relat_1(A_306))))
      | ~ v1_funct_1(A_306)
      | ~ v1_relat_1(A_306) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_416])).

tff(c_3666,plain,(
    ! [A_309] :
      ( m1_subset_1(k2_relat_1(A_309),k1_zfmisc_1(k2_relat_1(A_309)))
      | ~ v1_funct_1(A_309)
      | ~ v1_relat_1(A_309) ) ),
    inference(resolution,[status(thm)],[c_46,c_3614])).

tff(c_3697,plain,(
    ! [A_310] :
      ( r1_tarski(k2_relat_1(A_310),k2_relat_1(A_310))
      | ~ v1_funct_1(A_310)
      | ~ v1_relat_1(A_310) ) ),
    inference(resolution,[status(thm)],[c_3666,c_4])).

tff(c_3828,plain,(
    ! [A_319] :
      ( r1_tarski(k2_relat_1(k2_funct_1(A_319)),k1_relat_1(A_319))
      | ~ v1_funct_1(k2_funct_1(A_319))
      | ~ v1_relat_1(k2_funct_1(A_319))
      | ~ v2_funct_1(A_319)
      | ~ v1_funct_1(A_319)
      | ~ v1_relat_1(A_319) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3697])).

tff(c_3841,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_3828])).

tff(c_3854,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_107,c_3841])).

tff(c_3855,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3854])).

tff(c_3912,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_3855])).

tff(c_3916,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_3912])).

tff(c_3918,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3854])).

tff(c_618,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( k7_relset_1(A_97,B_98,C_99,D_100) = k9_relat_1(C_99,D_100)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_643,plain,(
    ! [D_100] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_100) = k9_relat_1('#skF_3',D_100) ),
    inference(resolution,[status(thm)],[c_64,c_618])).

tff(c_863,plain,(
    ! [A_119,B_120,C_121] :
      ( k7_relset_1(A_119,B_120,C_121,A_119) = k2_relset_1(A_119,B_120,C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_878,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_863])).

tff(c_887,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_60,c_878])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( k10_relat_1(B_8,k9_relat_1(B_8,A_7)) = A_7
      | ~ v2_funct_1(B_8)
      | ~ r1_tarski(A_7,k1_relat_1(B_8))
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1038,plain,(
    ! [A_7] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_7)) = A_7
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_7,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_14])).

tff(c_1091,plain,(
    ! [A_139] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_139)) = A_139
      | ~ r1_tarski(A_139,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_1038])).

tff(c_1100,plain,
    ( k10_relat_1('#skF_3','#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_887,c_1091])).

tff(c_1134,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1100])).

tff(c_2240,plain,(
    ! [A_222] :
      ( m1_subset_1(k2_relat_1(A_222),k1_zfmisc_1(k2_relat_1(A_222)))
      | ~ m1_subset_1(A_222,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_222),k2_relat_1(A_222))))
      | ~ v1_funct_1(A_222)
      | ~ v1_relat_1(A_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_416])).

tff(c_2283,plain,(
    ! [A_223] :
      ( m1_subset_1(k2_relat_1(A_223),k1_zfmisc_1(k2_relat_1(A_223)))
      | ~ v1_funct_1(A_223)
      | ~ v1_relat_1(A_223) ) ),
    inference(resolution,[status(thm)],[c_46,c_2240])).

tff(c_2336,plain,(
    ! [A_226] :
      ( r1_tarski(k2_relat_1(A_226),k2_relat_1(A_226))
      | ~ v1_funct_1(A_226)
      | ~ v1_relat_1(A_226) ) ),
    inference(resolution,[status(thm)],[c_2283,c_4])).

tff(c_2437,plain,(
    ! [A_230] :
      ( r1_tarski(k1_relat_1(A_230),k2_relat_1(k2_funct_1(A_230)))
      | ~ v1_funct_1(k2_funct_1(A_230))
      | ~ v1_relat_1(k2_funct_1(A_230))
      | ~ v2_funct_1(A_230)
      | ~ v1_funct_1(A_230)
      | ~ v1_relat_1(A_230) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2336])).

tff(c_2440,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_2437])).

tff(c_2448,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_107,c_2440])).

tff(c_2503,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2448])).

tff(c_2506,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_2503])).

tff(c_2510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_2506])).

tff(c_2511,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2448])).

tff(c_2515,plain,
    ( r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2511])).

tff(c_2517,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_1019,c_2515])).

tff(c_2519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1134,c_2517])).

tff(c_2520,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1100])).

tff(c_3917,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_3854])).

tff(c_926,plain,(
    ! [B_128,A_129] :
      ( m1_subset_1(B_128,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_128),A_129)))
      | ~ r1_tarski(k2_relat_1(B_128),A_129)
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_956,plain,(
    ! [B_128,A_129] :
      ( k2_relset_1(k1_relat_1(B_128),A_129,B_128) = k2_relat_1(B_128)
      | ~ r1_tarski(k2_relat_1(B_128),A_129)
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(resolution,[status(thm)],[c_926,c_26])).

tff(c_3926,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3917,c_956])).

tff(c_3941,plain,(
    k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3918,c_107,c_3926])).

tff(c_32,plain,(
    ! [A_26,B_27,C_28] :
      ( k7_relset_1(A_26,B_27,C_28,A_26) = k2_relset_1(A_26,B_27,C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4008,plain,(
    ! [B_326,A_327] :
      ( k7_relset_1(k1_relat_1(B_326),A_327,B_326,k1_relat_1(B_326)) = k2_relset_1(k1_relat_1(B_326),A_327,B_326)
      | ~ r1_tarski(k2_relat_1(B_326),A_327)
      | ~ v1_funct_1(B_326)
      | ~ v1_relat_1(B_326) ) ),
    inference(resolution,[status(thm)],[c_926,c_32])).

tff(c_28,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( k7_relset_1(A_22,B_23,C_24,D_25) = k9_relat_1(C_24,D_25)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_954,plain,(
    ! [B_128,A_129,D_25] :
      ( k7_relset_1(k1_relat_1(B_128),A_129,B_128,D_25) = k9_relat_1(B_128,D_25)
      | ~ r1_tarski(k2_relat_1(B_128),A_129)
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(resolution,[status(thm)],[c_926,c_28])).

tff(c_3922,plain,(
    ! [D_25] :
      ( k7_relset_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1',k2_funct_1('#skF_3'),D_25) = k9_relat_1(k2_funct_1('#skF_3'),D_25)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3917,c_954])).

tff(c_3935,plain,(
    ! [D_25] : k7_relset_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1',k2_funct_1('#skF_3'),D_25) = k9_relat_1(k2_funct_1('#skF_3'),D_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3918,c_107,c_3922])).

tff(c_4015,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1',k2_funct_1('#skF_3')) = k9_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4008,c_3935])).

tff(c_4060,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3918,c_107,c_3917,c_3941,c_4015])).

tff(c_4090,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4060])).

tff(c_4104,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_241,c_4090])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( k9_relat_1(k2_funct_1(B_6),A_5) = k10_relat_1(B_6,A_5)
      | ~ v2_funct_1(B_6)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4108,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4104,c_12])).

tff(c_4115,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_2520,c_4108])).

tff(c_208,plain,(
    ! [A_66] :
      ( m1_subset_1(A_66,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_66),k2_relat_1(A_66))))
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_226,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,k2_zfmisc_1(k1_relat_1(A_66),k2_relat_1(A_66)))
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_208,c_4])).

tff(c_4181,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4115,c_226])).

tff(c_4235,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3918,c_107,c_4181])).

tff(c_4420,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4235])).

tff(c_4440,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_241,c_4420])).

tff(c_4442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_4440])).

tff(c_4443,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1018])).

tff(c_4813,plain,(
    ! [A_366,A_367] :
      ( A_366 = '#skF_2'
      | ~ v1_funct_2(A_366,A_367,'#skF_2')
      | A_367 = '#skF_2'
      | ~ r1_tarski(A_366,k2_zfmisc_1(A_367,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4443,c_4443,c_4443,c_4443,c_528])).

tff(c_4827,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_116,c_4813])).

tff(c_4836,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4827])).

tff(c_4851,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4836])).

tff(c_814,plain,(
    ! [B_107] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_107) ),
    inference(splitLeft,[status(thm)],[c_767])).

tff(c_4450,plain,(
    ! [B_107] : ~ v1_funct_2('#skF_2','#skF_2',B_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4443,c_4443,c_814])).

tff(c_4863,plain,(
    ! [B_107] : ~ v1_funct_2('#skF_1','#skF_1',B_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4851,c_4851,c_4450])).

tff(c_4444,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1018])).

tff(c_4824,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_273,c_4813])).

tff(c_4833,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_4824])).

tff(c_5108,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4851,c_4851,c_4833])).

tff(c_5109,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_4444,c_5108])).

tff(c_4890,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4851,c_66])).

tff(c_5116,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5109,c_4890])).

tff(c_5127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4863,c_5116])).

tff(c_5128,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4836])).

tff(c_704,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_48])).

tff(c_716,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_704])).

tff(c_813,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_716])).

tff(c_4451,plain,(
    ~ v1_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4443,c_813])).

tff(c_5147,plain,(
    ~ v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5128,c_4451])).

tff(c_5171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5147])).

tff(c_5172,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_767])).

tff(c_8618,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8610,c_8610,c_5172])).

tff(c_9030,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9002,c_9002,c_8618])).

tff(c_8611,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5502])).

tff(c_8990,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_273,c_8979])).

tff(c_8998,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_8990])).

tff(c_9316,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9002,c_9002,c_8998])).

tff(c_9317,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_8611,c_9316])).

tff(c_9326,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9317,c_8611])).

tff(c_9339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9030,c_9326])).

tff(c_9340,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9001])).

tff(c_8619,plain,(
    ~ v1_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8610,c_813])).

tff(c_9358,plain,(
    ~ v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9340,c_8619])).

tff(c_9382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_9358])).

tff(c_9384,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_716])).

tff(c_12682,plain,(
    v1_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12673,c_9384])).

tff(c_638,plain,(
    ! [A_97,B_98,D_100] : k7_relset_1(A_97,B_98,k2_relat_1(k1_xboole_0),D_100) = k9_relat_1(k2_relat_1(k1_xboole_0),D_100) ),
    inference(resolution,[status(thm)],[c_469,c_618])).

tff(c_9474,plain,(
    ! [A_641,B_642,D_643] : k7_relset_1(A_641,B_642,k1_xboole_0,D_643) = k9_relat_1(k1_xboole_0,D_643) ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_673,c_638])).

tff(c_471,plain,(
    ! [B_85] : m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(B_85)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_463])).

tff(c_487,plain,(
    ! [A_19,B_20] : k2_relset_1(A_19,B_20,k2_relat_1(k1_xboole_0)) = k2_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_471,c_26])).

tff(c_678,plain,(
    ! [A_19,B_20] : k2_relset_1(A_19,B_20,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_673,c_673,c_487])).

tff(c_9422,plain,(
    ! [A_634,B_635,C_636] :
      ( k7_relset_1(A_634,B_635,C_636,A_634) = k2_relset_1(A_634,B_635,C_636)
      | ~ m1_subset_1(C_636,k1_zfmisc_1(k2_zfmisc_1(A_634,B_635))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_9425,plain,(
    ! [A_634,B_635] : k7_relset_1(A_634,B_635,k1_xboole_0,A_634) = k2_relset_1(A_634,B_635,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_682,c_9422])).

tff(c_9439,plain,(
    ! [A_634,B_635] : k7_relset_1(A_634,B_635,k1_xboole_0,A_634) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_9425])).

tff(c_9480,plain,(
    ! [D_643] : k9_relat_1(k1_xboole_0,D_643) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9474,c_9439])).

tff(c_12677,plain,(
    ! [D_643] : k9_relat_1('#skF_2',D_643) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12673,c_12673,c_9480])).

tff(c_9543,plain,(
    ! [B_650,A_651] :
      ( k10_relat_1(B_650,k9_relat_1(B_650,A_651)) = A_651
      | ~ v2_funct_1(B_650)
      | ~ r1_tarski(A_651,k1_relat_1(B_650))
      | ~ v1_funct_1(B_650)
      | ~ v1_relat_1(B_650) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_9549,plain,(
    ! [B_650] :
      ( k10_relat_1(B_650,k9_relat_1(B_650,k1_xboole_0)) = k1_xboole_0
      | ~ v2_funct_1(B_650)
      | ~ v1_funct_1(B_650)
      | ~ v1_relat_1(B_650) ) ),
    inference(resolution,[status(thm)],[c_2,c_9543])).

tff(c_13014,plain,(
    ! [B_871] :
      ( k10_relat_1(B_871,k9_relat_1(B_871,'#skF_2')) = '#skF_2'
      | ~ v2_funct_1(B_871)
      | ~ v1_funct_1(B_871)
      | ~ v1_relat_1(B_871) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12673,c_12673,c_9549])).

tff(c_13024,plain,
    ( k10_relat_1('#skF_2','#skF_2') = '#skF_2'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12677,c_13014])).

tff(c_13032,plain,
    ( k10_relat_1('#skF_2','#skF_2') = '#skF_2'
    | ~ v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12691,c_12682,c_13024])).

tff(c_13033,plain,(
    ~ v2_funct_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_13032])).

tff(c_13341,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13338,c_13033])).

tff(c_13382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_13341])).

tff(c_13383,plain,(
    k10_relat_1('#skF_2','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_13032])).

tff(c_13724,plain,(
    k10_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13721,c_13721,c_13721,c_13383])).

tff(c_13756,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13721,c_241])).

tff(c_15132,plain,(
    ! [A_1000] :
      ( v1_funct_2(k2_funct_1(A_1000),k2_relat_1(A_1000),k2_relat_1(k2_funct_1(A_1000)))
      | ~ v1_funct_1(k2_funct_1(A_1000))
      | ~ v1_relat_1(k2_funct_1(A_1000))
      | ~ v2_funct_1(A_1000)
      | ~ v1_funct_1(A_1000)
      | ~ v1_relat_1(A_1000) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_48])).

tff(c_15135,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13756,c_15132])).

tff(c_15143,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_107,c_15135])).

tff(c_15144,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_15143])).

tff(c_15147,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_15144])).

tff(c_15151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_15147])).

tff(c_15153,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_15143])).

tff(c_15152,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_15143])).

tff(c_15156,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_15152])).

tff(c_15158,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_15156])).

tff(c_324,plain,(
    ! [A_77] :
      ( r1_tarski(A_77,k2_zfmisc_1(k1_relat_1(A_77),k2_relat_1(A_77)))
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(resolution,[status(thm)],[c_208,c_4])).

tff(c_15159,plain,(
    ! [A_1001] :
      ( r1_tarski(k2_funct_1(A_1001),k2_zfmisc_1(k2_relat_1(A_1001),k2_relat_1(k2_funct_1(A_1001))))
      | ~ v1_funct_1(k2_funct_1(A_1001))
      | ~ v1_relat_1(k2_funct_1(A_1001))
      | ~ v2_funct_1(A_1001)
      | ~ v1_funct_1(A_1001)
      | ~ v1_relat_1(A_1001) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_324])).

tff(c_15183,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13756,c_15159])).

tff(c_15199,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_15153,c_107,c_15183])).

tff(c_15229,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',k1_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_15199])).

tff(c_15248,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_15229])).

tff(c_13744,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13721,c_12673])).

tff(c_13965,plain,(
    ! [B_107,A_2] :
      ( k1_relset_1('#skF_3',B_107,A_2) = '#skF_3'
      | ~ v1_funct_2(A_2,'#skF_3',B_107)
      | ~ r1_tarski(A_2,k2_zfmisc_1('#skF_3',B_107)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13744,c_13744,c_13744,c_13744,c_769])).

tff(c_15312,plain,
    ( k1_relset_1('#skF_3',k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15248,c_13965])).

tff(c_15337,plain,(
    k1_relset_1('#skF_3',k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15158,c_15312])).

tff(c_15249,plain,(
    ! [A_1002] :
      ( m1_subset_1(k2_funct_1(A_1002),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1002),k2_relat_1(k2_funct_1(A_1002)))))
      | ~ v1_funct_1(k2_funct_1(A_1002))
      | ~ v1_relat_1(k2_funct_1(A_1002))
      | ~ v2_funct_1(A_1002)
      | ~ v1_funct_1(A_1002)
      | ~ v1_relat_1(A_1002) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_208])).

tff(c_15278,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13756,c_15249])).

tff(c_15296,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_15153,c_107,c_15278])).

tff(c_15382,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_15296])).

tff(c_15404,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_15382])).

tff(c_15440,plain,(
    k1_relset_1('#skF_3',k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15404,c_24])).

tff(c_15468,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15337,c_15440])).

tff(c_641,plain,(
    ! [A_32,D_100] :
      ( k7_relset_1(k1_relat_1(A_32),k2_relat_1(A_32),A_32,D_100) = k9_relat_1(A_32,D_100)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(resolution,[status(thm)],[c_46,c_618])).

tff(c_14705,plain,(
    ! [A_977] :
      ( k7_relset_1(k1_relat_1(A_977),k2_relat_1(A_977),A_977,k1_relat_1(A_977)) = k2_relset_1(k1_relat_1(A_977),k2_relat_1(A_977),A_977)
      | ~ v1_funct_1(A_977)
      | ~ v1_relat_1(A_977) ) ),
    inference(resolution,[status(thm)],[c_46,c_9422])).

tff(c_14855,plain,(
    ! [A_986] :
      ( k2_relset_1(k1_relat_1(A_986),k2_relat_1(A_986),A_986) = k9_relat_1(A_986,k1_relat_1(A_986))
      | ~ v1_funct_1(A_986)
      | ~ v1_relat_1(A_986)
      | ~ v1_funct_1(A_986)
      | ~ v1_relat_1(A_986) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_14705])).

tff(c_14877,plain,(
    ! [A_986] :
      ( k9_relat_1(A_986,k1_relat_1(A_986)) = k2_relat_1(A_986)
      | ~ v1_funct_1(A_986)
      | ~ v1_relat_1(A_986)
      | ~ v1_funct_1(A_986)
      | ~ v1_relat_1(A_986)
      | ~ v1_funct_1(A_986)
      | ~ v1_relat_1(A_986) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14855,c_238])).

tff(c_15503,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15468,c_14877])).

tff(c_15581,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15153,c_107,c_15153,c_107,c_15153,c_107,c_15503])).

tff(c_15627,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15581,c_12])).

tff(c_15636,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_13724,c_15627])).

tff(c_15790,plain,
    ( k1_relat_1('#skF_3') = '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15636,c_16])).

tff(c_15862,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_15790])).

tff(c_15864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13738,c_15862])).

tff(c_15865,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_767])).

tff(c_19454,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19446,c_19446,c_15865])).

tff(c_20407,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20392,c_20392,c_19454])).

tff(c_19447,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16102])).

tff(c_20380,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_273,c_20369])).

tff(c_20388,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_20380])).

tff(c_20729,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20392,c_20392,c_20388])).

tff(c_20730,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_19447,c_20729])).

tff(c_20739,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20730,c_19447])).

tff(c_20753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20407,c_20739])).

tff(c_20754,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20391])).

tff(c_19459,plain,(
    ! [B_83] : m1_subset_1('#skF_2',k1_zfmisc_1(B_83)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19446,c_682])).

tff(c_20768,plain,(
    ! [B_83] : m1_subset_1('#skF_3',k1_zfmisc_1(B_83)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20754,c_19459])).

tff(c_20788,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20754,c_241])).

tff(c_22166,plain,(
    ! [A_1382] :
      ( v1_funct_2(k2_funct_1(A_1382),k2_relat_1(A_1382),k2_relat_1(k2_funct_1(A_1382)))
      | ~ v1_funct_1(k2_funct_1(A_1382))
      | ~ v1_relat_1(k2_funct_1(A_1382))
      | ~ v2_funct_1(A_1382)
      | ~ v1_funct_1(A_1382)
      | ~ v1_relat_1(A_1382) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_48])).

tff(c_22169,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20788,c_22166])).

tff(c_22177,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_107,c_22169])).

tff(c_22178,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_22177])).

tff(c_22181,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_22178])).

tff(c_22185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_22181])).

tff(c_22187,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_22177])).

tff(c_19464,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19446,c_2])).

tff(c_20772,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20754,c_19464])).

tff(c_20770,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20754,c_20754,c_19454])).

tff(c_21971,plain,(
    ! [A_1375] :
      ( m1_subset_1(k2_relat_1(A_1375),k1_zfmisc_1(k2_relat_1(A_1375)))
      | ~ m1_subset_1(A_1375,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1375),k2_relat_1(A_1375))))
      | ~ v1_funct_1(A_1375)
      | ~ v1_relat_1(A_1375) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_416])).

tff(c_22009,plain,(
    ! [A_1376] :
      ( m1_subset_1(k2_relat_1(A_1376),k1_zfmisc_1(k2_relat_1(A_1376)))
      | ~ v1_funct_1(A_1376)
      | ~ v1_relat_1(A_1376) ) ),
    inference(resolution,[status(thm)],[c_46,c_21971])).

tff(c_22030,plain,(
    ! [A_1377] :
      ( r1_tarski(k2_relat_1(A_1377),k2_relat_1(A_1377))
      | ~ v1_funct_1(A_1377)
      | ~ v1_relat_1(A_1377) ) ),
    inference(resolution,[status(thm)],[c_22009,c_4])).

tff(c_22205,plain,(
    ! [A_1384] :
      ( r1_tarski(k2_relat_1(k2_funct_1(A_1384)),k1_relat_1(A_1384))
      | ~ v1_funct_1(k2_funct_1(A_1384))
      | ~ v1_relat_1(k2_funct_1(A_1384))
      | ~ v2_funct_1(A_1384)
      | ~ v1_funct_1(A_1384)
      | ~ v1_relat_1(A_1384) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_22030])).

tff(c_22218,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20770,c_22205])).

tff(c_22231,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_22187,c_107,c_22218])).

tff(c_19841,plain,(
    ! [A_1246,A_1247] :
      ( A_1246 = '#skF_2'
      | ~ v1_funct_2(A_1246,A_1247,'#skF_2')
      | A_1247 = '#skF_2'
      | ~ r1_tarski(A_1246,k2_zfmisc_1(A_1247,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19446,c_19446,c_19446,c_19446,c_528])).

tff(c_19855,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_116,c_19841])).

tff(c_19863,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_19855])).

tff(c_19864,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_19863])).

tff(c_19877,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19864,c_19864,c_19454])).

tff(c_19852,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_273,c_19841])).

tff(c_19860,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_19852])).

tff(c_20181,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19864,c_19864,c_19860])).

tff(c_20182,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_19447,c_20181])).

tff(c_20191,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20182,c_19447])).

tff(c_20205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19877,c_20191])).

tff(c_20206,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_19863])).

tff(c_19463,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19446,c_137])).

tff(c_19455,plain,(
    v1_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19446,c_9384])).

tff(c_16018,plain,(
    ! [A_1016,B_1017,D_1018] : k7_relset_1(A_1016,B_1017,k1_xboole_0,D_1018) = k9_relat_1(k1_xboole_0,D_1018) ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_673,c_638])).

tff(c_15931,plain,(
    ! [A_1007,B_1008,C_1009] :
      ( k7_relset_1(A_1007,B_1008,C_1009,A_1007) = k2_relset_1(A_1007,B_1008,C_1009)
      | ~ m1_subset_1(C_1009,k1_zfmisc_1(k2_zfmisc_1(A_1007,B_1008))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_15934,plain,(
    ! [A_1007,B_1008] : k7_relset_1(A_1007,B_1008,k1_xboole_0,A_1007) = k2_relset_1(A_1007,B_1008,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_682,c_15931])).

tff(c_15948,plain,(
    ! [A_1007,B_1008] : k7_relset_1(A_1007,B_1008,k1_xboole_0,A_1007) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_15934])).

tff(c_16024,plain,(
    ! [D_1018] : k9_relat_1(k1_xboole_0,D_1018) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16018,c_15948])).

tff(c_19450,plain,(
    ! [D_1018] : k9_relat_1('#skF_2',D_1018) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19446,c_19446,c_16024])).

tff(c_16050,plain,(
    ! [B_1023,A_1024] :
      ( k10_relat_1(B_1023,k9_relat_1(B_1023,A_1024)) = A_1024
      | ~ v2_funct_1(B_1023)
      | ~ r1_tarski(A_1024,k1_relat_1(B_1023))
      | ~ v1_funct_1(B_1023)
      | ~ v1_relat_1(B_1023) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16060,plain,(
    ! [B_1023] :
      ( k10_relat_1(B_1023,k9_relat_1(B_1023,k1_xboole_0)) = k1_xboole_0
      | ~ v2_funct_1(B_1023)
      | ~ v1_funct_1(B_1023)
      | ~ v1_relat_1(B_1023) ) ),
    inference(resolution,[status(thm)],[c_2,c_16050])).

tff(c_19707,plain,(
    ! [B_1235] :
      ( k10_relat_1(B_1235,k9_relat_1(B_1235,'#skF_2')) = '#skF_2'
      | ~ v2_funct_1(B_1235)
      | ~ v1_funct_1(B_1235)
      | ~ v1_relat_1(B_1235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19446,c_19446,c_16060])).

tff(c_19717,plain,
    ( k10_relat_1('#skF_2','#skF_2') = '#skF_2'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_19450,c_19707])).

tff(c_19725,plain,
    ( k10_relat_1('#skF_2','#skF_2') = '#skF_2'
    | ~ v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19463,c_19455,c_19717])).

tff(c_19739,plain,(
    ~ v2_funct_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_19725])).

tff(c_20210,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20206,c_19739])).

tff(c_20248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_20210])).

tff(c_20250,plain,(
    v2_funct_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_19725])).

tff(c_20249,plain,(
    k10_relat_1('#skF_2','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_19725])).

tff(c_16052,plain,(
    ! [A_1024] :
      ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,A_1024)) = A_1024
      | ~ v2_funct_1(k1_xboole_0)
      | ~ r1_tarski(A_1024,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15865,c_16050])).

tff(c_16059,plain,(
    ! [A_1024] :
      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = A_1024
      | ~ v2_funct_1(k1_xboole_0)
      | ~ r1_tarski(A_1024,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_9384,c_16024,c_16052])).

tff(c_20313,plain,(
    ! [A_1024] :
      ( A_1024 = '#skF_2'
      | ~ r1_tarski(A_1024,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19446,c_20250,c_19446,c_20249,c_19446,c_19446,c_16059])).

tff(c_20757,plain,(
    ! [A_1024] :
      ( A_1024 = '#skF_3'
      | ~ r1_tarski(A_1024,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20754,c_20754,c_20313])).

tff(c_22269,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_22231,c_20757])).

tff(c_54,plain,(
    ! [B_34,A_33] :
      ( v1_funct_2(B_34,k1_relat_1(B_34),A_33)
      | ~ r1_tarski(k2_relat_1(B_34),A_33)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_20776,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20754,c_19446])).

tff(c_36,plain,(
    ! [C_31,A_29] :
      ( k1_xboole_0 = C_31
      | ~ v1_funct_2(C_31,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_16003,plain,(
    ! [B_1012] :
      ( k1_xboole_0 = B_1012
      | ~ v1_funct_2(B_1012,k1_relat_1(B_1012),k1_xboole_0)
      | k1_relat_1(B_1012) = k1_xboole_0
      | ~ r1_tarski(k2_relat_1(B_1012),k1_xboole_0)
      | ~ v1_funct_1(B_1012)
      | ~ v1_relat_1(B_1012) ) ),
    inference(resolution,[status(thm)],[c_15971,c_36])).

tff(c_21800,plain,(
    ! [B_1365] :
      ( B_1365 = '#skF_3'
      | ~ v1_funct_2(B_1365,k1_relat_1(B_1365),'#skF_3')
      | k1_relat_1(B_1365) = '#skF_3'
      | ~ r1_tarski(k2_relat_1(B_1365),'#skF_3')
      | ~ v1_funct_1(B_1365)
      | ~ v1_relat_1(B_1365) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20776,c_20776,c_20776,c_20776,c_16003])).

tff(c_21830,plain,(
    ! [B_34] :
      ( B_34 = '#skF_3'
      | k1_relat_1(B_34) = '#skF_3'
      | ~ r1_tarski(k2_relat_1(B_34),'#skF_3')
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_54,c_21800])).

tff(c_22236,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22231,c_21830])).

tff(c_22256,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22187,c_107,c_22236])).

tff(c_22432,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_22256])).

tff(c_16007,plain,(
    ! [B_1012,A_1013] :
      ( r1_tarski(B_1012,k2_zfmisc_1(k1_relat_1(B_1012),A_1013))
      | ~ r1_tarski(k2_relat_1(B_1012),A_1013)
      | ~ v1_funct_1(B_1012)
      | ~ v1_relat_1(B_1012) ) ),
    inference(resolution,[status(thm)],[c_15971,c_4])).

tff(c_22556,plain,(
    ! [A_1013] :
      ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',A_1013))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1013)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22432,c_16007])).

tff(c_22616,plain,(
    ! [A_1013] : r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',A_1013)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22187,c_107,c_20772,c_22269,c_22556])).

tff(c_20789,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20754,c_189])).

tff(c_22663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22616,c_20789])).

tff(c_22664,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22256])).

tff(c_20790,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20754,c_185])).

tff(c_22670,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22664,c_20790])).

tff(c_22679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20768,c_22670])).

tff(c_22681,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_526])).

tff(c_27465,plain,(
    k2_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27447,c_27447,c_22681])).

tff(c_27997,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27975,c_27975,c_27465])).

tff(c_27448,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_23111])).

tff(c_27958,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_273,c_27935])).

tff(c_27971,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_27958])).

tff(c_28180,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27975,c_27975,c_27971])).

tff(c_28181,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_27448,c_28180])).

tff(c_28014,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27975,c_241])).

tff(c_28187,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28181,c_28014])).

tff(c_28196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27997,c_28187])).

tff(c_28197,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_27974])).

tff(c_28237,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28197,c_241])).

tff(c_28220,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28197,c_28197,c_27465])).

tff(c_28306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28237,c_28220])).

tff(c_28307,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_28308,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_20,plain,(
    ! [C_12,A_10,B_11] :
      ( v1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28319,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28308,c_20])).

tff(c_28387,plain,(
    ! [A_1729,B_1730,C_1731] :
      ( k2_relset_1(A_1729,B_1730,C_1731) = k2_relat_1(C_1731)
      | ~ m1_subset_1(C_1731,k1_zfmisc_1(k2_zfmisc_1(A_1729,B_1730))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28400,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_28387])).

tff(c_28405,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_28400])).

tff(c_28318,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28308,c_24])).

tff(c_29156,plain,(
    ! [B_1790,C_1791,A_1792] :
      ( k1_xboole_0 = B_1790
      | v1_funct_2(C_1791,A_1792,B_1790)
      | k1_relset_1(A_1792,B_1790,C_1791) != A_1792
      | ~ m1_subset_1(C_1791,k1_zfmisc_1(k2_zfmisc_1(A_1792,B_1790))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_29176,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_28308,c_29156])).

tff(c_29193,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28318,c_29176])).

tff(c_29194,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_28307,c_29193])).

tff(c_29198,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_29194])).

tff(c_29201,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_29198])).

tff(c_29204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_28405,c_29201])).

tff(c_29206,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_29194])).

tff(c_29205,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_29194])).

tff(c_44,plain,(
    ! [B_30,A_29,C_31] :
      ( k1_xboole_0 = B_30
      | k1_relset_1(A_29,B_30,C_31) = A_29
      | ~ v1_funct_2(C_31,A_29,B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_29314,plain,(
    ! [B_1794,A_1795,C_1796] :
      ( B_1794 = '#skF_1'
      | k1_relset_1(A_1795,B_1794,C_1796) = A_1795
      | ~ v1_funct_2(C_1796,A_1795,B_1794)
      | ~ m1_subset_1(C_1796,k1_zfmisc_1(k2_zfmisc_1(A_1795,B_1794))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29205,c_44])).

tff(c_29337,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_29314])).

tff(c_29348,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_180,c_29337])).

tff(c_29397,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_29348])).

tff(c_28685,plain,(
    ! [A_1755,B_1756,C_1757,D_1758] :
      ( k7_relset_1(A_1755,B_1756,C_1757,D_1758) = k9_relat_1(C_1757,D_1758)
      | ~ m1_subset_1(C_1757,k1_zfmisc_1(k2_zfmisc_1(A_1755,B_1756))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28711,plain,(
    ! [D_1758] : k7_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3'),D_1758) = k9_relat_1(k2_funct_1('#skF_3'),D_1758) ),
    inference(resolution,[status(thm)],[c_28308,c_28685])).

tff(c_28402,plain,(
    k2_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28308,c_28387])).

tff(c_28981,plain,(
    ! [A_1781,B_1782,C_1783] :
      ( k7_relset_1(A_1781,B_1782,C_1783,A_1781) = k2_relset_1(A_1781,B_1782,C_1783)
      | ~ m1_subset_1(C_1783,k1_zfmisc_1(k2_zfmisc_1(A_1781,B_1782))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28995,plain,(
    k7_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3'),'#skF_2') = k2_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28308,c_28981])).

tff(c_29009,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28711,c_28402,c_28995])).

tff(c_29039,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29009,c_12])).

tff(c_29046,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_29039])).

tff(c_29070,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29046,c_16])).

tff(c_29084,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_29070])).

tff(c_29091,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29084,c_29046])).

tff(c_29399,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29397,c_29091])).

tff(c_29467,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29399,c_48])).

tff(c_29480,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28319,c_107,c_29206,c_29467])).

tff(c_29482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28307,c_29480])).

tff(c_29484,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_29348])).

tff(c_29483,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_29348])).

tff(c_29488,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29483,c_29084])).

tff(c_28713,plain,(
    ! [D_1758] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_1758) = k9_relat_1('#skF_3',D_1758) ),
    inference(resolution,[status(thm)],[c_64,c_28685])).

tff(c_29000,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_28981])).

tff(c_29012,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28713,c_60,c_29000])).

tff(c_29490,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29483,c_29012])).

tff(c_29050,plain,(
    ! [B_1788,A_1789] :
      ( k10_relat_1(B_1788,k9_relat_1(B_1788,A_1789)) = A_1789
      | ~ v2_funct_1(B_1788)
      | ~ r1_tarski(A_1789,k1_relat_1(B_1788))
      | ~ v1_funct_1(B_1788)
      | ~ v1_relat_1(B_1788) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_29056,plain,(
    ! [B_1788] :
      ( k10_relat_1(B_1788,k9_relat_1(B_1788,k1_xboole_0)) = k1_xboole_0
      | ~ v2_funct_1(B_1788)
      | ~ v1_funct_1(B_1788)
      | ~ v1_relat_1(B_1788) ) ),
    inference(resolution,[status(thm)],[c_2,c_29050])).

tff(c_29922,plain,(
    ! [B_1810] :
      ( k10_relat_1(B_1810,k9_relat_1(B_1810,'#skF_1')) = '#skF_1'
      | ~ v2_funct_1(B_1810)
      | ~ v1_funct_1(B_1810)
      | ~ v1_relat_1(B_1810) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29205,c_29205,c_29056])).

tff(c_29934,plain,
    ( k10_relat_1('#skF_3','#skF_1') = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29490,c_29922])).

tff(c_29948,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_68,c_62,c_29488,c_29934])).

tff(c_29950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29484,c_29948])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.65/4.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.12/4.61  
% 12.12/4.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.12/4.62  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.12/4.62  
% 12.12/4.62  %Foreground sorts:
% 12.12/4.62  
% 12.12/4.62  
% 12.12/4.62  %Background operators:
% 12.12/4.62  
% 12.12/4.62  
% 12.12/4.62  %Foreground operators:
% 12.12/4.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.12/4.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.12/4.62  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.12/4.62  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.12/4.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.12/4.62  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 12.12/4.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.12/4.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.12/4.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.12/4.62  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 12.12/4.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.12/4.62  tff('#skF_2', type, '#skF_2': $i).
% 12.12/4.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.12/4.62  tff('#skF_3', type, '#skF_3': $i).
% 12.12/4.62  tff('#skF_1', type, '#skF_1': $i).
% 12.12/4.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.12/4.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.12/4.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.12/4.62  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 12.12/4.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.12/4.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.12/4.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.12/4.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.12/4.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.12/4.62  
% 12.46/4.67  tff(f_150, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 12.46/4.67  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 12.46/4.67  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 12.46/4.67  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.46/4.67  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.46/4.67  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 12.46/4.67  tff(f_121, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 12.46/4.67  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.46/4.67  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 12.46/4.67  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 12.46/4.67  tff(f_133, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 12.46/4.67  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.46/4.67  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 12.46/4.67  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 12.46/4.67  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 12.46/4.67  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 12.46/4.67  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.46/4.67  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.46/4.67  tff(c_108, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.46/4.67  tff(c_116, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_108])).
% 12.46/4.67  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.46/4.67  tff(c_8, plain, (![A_4]: (v1_funct_1(k2_funct_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.46/4.67  tff(c_58, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.46/4.67  tff(c_77, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_58])).
% 12.46/4.67  tff(c_80, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_77])).
% 12.46/4.67  tff(c_83, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_80])).
% 12.46/4.67  tff(c_93, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.46/4.67  tff(c_100, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_93])).
% 12.46/4.67  tff(c_105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_100])).
% 12.46/4.67  tff(c_106, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_58])).
% 12.46/4.67  tff(c_185, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_106])).
% 12.46/4.67  tff(c_117, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.46/4.67  tff(c_126, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_117])).
% 12.46/4.67  tff(c_62, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.46/4.67  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.46/4.67  tff(c_227, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.46/4.67  tff(c_237, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_227])).
% 12.46/4.67  tff(c_241, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_237])).
% 12.46/4.67  tff(c_18, plain, (![A_9]: (k1_relat_1(k2_funct_1(A_9))=k2_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.46/4.67  tff(c_10, plain, (![A_4]: (v1_relat_1(k2_funct_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.46/4.67  tff(c_107, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_58])).
% 12.46/4.67  tff(c_151, plain, (![A_55]: (k1_relat_1(k2_funct_1(A_55))=k2_relat_1(A_55) | ~v2_funct_1(A_55) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.46/4.67  tff(c_48, plain, (![A_32]: (v1_funct_2(A_32, k1_relat_1(A_32), k2_relat_1(A_32)) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.46/4.67  tff(c_27085, plain, (![A_1674]: (v1_funct_2(k2_funct_1(A_1674), k2_relat_1(A_1674), k2_relat_1(k2_funct_1(A_1674))) | ~v1_funct_1(k2_funct_1(A_1674)) | ~v1_relat_1(k2_funct_1(A_1674)) | ~v2_funct_1(A_1674) | ~v1_funct_1(A_1674) | ~v1_relat_1(A_1674))), inference(superposition, [status(thm), theory('equality')], [c_151, c_48])).
% 12.46/4.67  tff(c_27091, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_241, c_27085])).
% 12.46/4.67  tff(c_27101, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_107, c_27091])).
% 12.46/4.67  tff(c_27102, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_27101])).
% 12.46/4.67  tff(c_27105, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_27102])).
% 12.46/4.67  tff(c_27109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_27105])).
% 12.46/4.67  tff(c_27111, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_27101])).
% 12.46/4.67  tff(c_171, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.46/4.67  tff(c_180, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_171])).
% 12.46/4.67  tff(c_23064, plain, (![B_1425, A_1426, C_1427]: (k1_xboole_0=B_1425 | k1_relset_1(A_1426, B_1425, C_1427)=A_1426 | ~v1_funct_2(C_1427, A_1426, B_1425) | ~m1_subset_1(C_1427, k1_zfmisc_1(k2_zfmisc_1(A_1426, B_1425))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.46/4.67  tff(c_23096, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_23064])).
% 12.46/4.67  tff(c_23111, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_180, c_23096])).
% 12.46/4.67  tff(c_23112, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_23111])).
% 12.46/4.67  tff(c_16, plain, (![A_9]: (k2_relat_1(k2_funct_1(A_9))=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.46/4.67  tff(c_46, plain, (![A_32]: (m1_subset_1(A_32, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_32), k2_relat_1(A_32)))) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.46/4.67  tff(c_238, plain, (![A_32]: (k2_relset_1(k1_relat_1(A_32), k2_relat_1(A_32), A_32)=k2_relat_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(resolution, [status(thm)], [c_46, c_227])).
% 12.46/4.67  tff(c_416, plain, (![A_80, B_81, C_82]: (m1_subset_1(k2_relset_1(A_80, B_81, C_82), k1_zfmisc_1(B_81)) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.46/4.67  tff(c_26768, plain, (![A_1666]: (m1_subset_1(k2_relat_1(A_1666), k1_zfmisc_1(k2_relat_1(A_1666))) | ~m1_subset_1(A_1666, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1666), k2_relat_1(A_1666)))) | ~v1_funct_1(A_1666) | ~v1_relat_1(A_1666))), inference(superposition, [status(thm), theory('equality')], [c_238, c_416])).
% 12.46/4.67  tff(c_26818, plain, (![A_1667]: (m1_subset_1(k2_relat_1(A_1667), k1_zfmisc_1(k2_relat_1(A_1667))) | ~v1_funct_1(A_1667) | ~v1_relat_1(A_1667))), inference(resolution, [status(thm)], [c_46, c_26768])).
% 12.46/4.67  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(A_2, B_3) | ~m1_subset_1(A_2, k1_zfmisc_1(B_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.46/4.67  tff(c_26849, plain, (![A_1668]: (r1_tarski(k2_relat_1(A_1668), k2_relat_1(A_1668)) | ~v1_funct_1(A_1668) | ~v1_relat_1(A_1668))), inference(resolution, [status(thm)], [c_26818, c_4])).
% 12.46/4.67  tff(c_27117, plain, (![A_1675]: (r1_tarski(k2_relat_1(k2_funct_1(A_1675)), k1_relat_1(A_1675)) | ~v1_funct_1(k2_funct_1(A_1675)) | ~v1_relat_1(k2_funct_1(A_1675)) | ~v2_funct_1(A_1675) | ~v1_funct_1(A_1675) | ~v1_relat_1(A_1675))), inference(superposition, [status(thm), theory('equality')], [c_16, c_26849])).
% 12.46/4.67  tff(c_27130, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23112, c_27117])).
% 12.46/4.67  tff(c_27143, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_27111, c_107, c_27130])).
% 12.46/4.67  tff(c_52, plain, (![B_34, A_33]: (m1_subset_1(B_34, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_34), A_33))) | ~r1_tarski(k2_relat_1(B_34), A_33) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_133])).
% 12.46/4.67  tff(c_22882, plain, (![B_1413, A_1414]: (m1_subset_1(B_1413, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1413), A_1414))) | ~r1_tarski(k2_relat_1(B_1413), A_1414) | ~v1_funct_1(B_1413) | ~v1_relat_1(B_1413))), inference(cnfTransformation, [status(thm)], [f_133])).
% 12.46/4.67  tff(c_26, plain, (![A_19, B_20, C_21]: (k2_relset_1(A_19, B_20, C_21)=k2_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.46/4.67  tff(c_22912, plain, (![B_1413, A_1414]: (k2_relset_1(k1_relat_1(B_1413), A_1414, B_1413)=k2_relat_1(B_1413) | ~r1_tarski(k2_relat_1(B_1413), A_1414) | ~v1_funct_1(B_1413) | ~v1_relat_1(B_1413))), inference(resolution, [status(thm)], [c_22882, c_26])).
% 12.46/4.67  tff(c_27149, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_27143, c_22912])).
% 12.46/4.67  tff(c_27163, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_27111, c_107, c_27149])).
% 12.46/4.67  tff(c_22, plain, (![A_13, B_14, C_15]: (m1_subset_1(k2_relset_1(A_13, B_14, C_15), k1_zfmisc_1(B_14)) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.46/4.67  tff(c_27178, plain, (m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_27163, c_22])).
% 12.46/4.67  tff(c_27268, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(splitLeft, [status(thm)], [c_27178])).
% 12.46/4.67  tff(c_27349, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_27268])).
% 12.46/4.67  tff(c_27359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27111, c_107, c_27143, c_27349])).
% 12.46/4.67  tff(c_27361, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(splitRight, [status(thm)], [c_27178])).
% 12.46/4.67  tff(c_27421, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_27361])).
% 12.46/4.67  tff(c_27444, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_241, c_27421])).
% 12.46/4.67  tff(c_27446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_27444])).
% 12.46/4.67  tff(c_27447, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_23111])).
% 12.46/4.67  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.46/4.67  tff(c_513, plain, (![C_89, A_90]: (k1_xboole_0=C_89 | ~v1_funct_2(C_89, A_90, k1_xboole_0) | k1_xboole_0=A_90 | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.46/4.67  tff(c_528, plain, (![A_2, A_90]: (k1_xboole_0=A_2 | ~v1_funct_2(A_2, A_90, k1_xboole_0) | k1_xboole_0=A_90 | ~r1_tarski(A_2, k2_zfmisc_1(A_90, k1_xboole_0)))), inference(resolution, [status(thm)], [c_6, c_513])).
% 12.46/4.67  tff(c_27935, plain, (![A_1711, A_1712]: (A_1711='#skF_2' | ~v1_funct_2(A_1711, A_1712, '#skF_2') | A_1712='#skF_2' | ~r1_tarski(A_1711, k2_zfmisc_1(A_1712, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_27447, c_27447, c_27447, c_27447, c_528])).
% 12.46/4.67  tff(c_27961, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_116, c_27935])).
% 12.46/4.67  tff(c_27974, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_27961])).
% 12.46/4.67  tff(c_27975, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_27974])).
% 12.46/4.67  tff(c_19083, plain, (![A_1211]: (v1_funct_2(k2_funct_1(A_1211), k2_relat_1(A_1211), k2_relat_1(k2_funct_1(A_1211))) | ~v1_funct_1(k2_funct_1(A_1211)) | ~v1_relat_1(k2_funct_1(A_1211)) | ~v2_funct_1(A_1211) | ~v1_funct_1(A_1211) | ~v1_relat_1(A_1211))), inference(superposition, [status(thm), theory('equality')], [c_151, c_48])).
% 12.46/4.67  tff(c_19089, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_241, c_19083])).
% 12.46/4.67  tff(c_19099, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_107, c_19089])).
% 12.46/4.67  tff(c_19100, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_19099])).
% 12.46/4.67  tff(c_19103, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_19100])).
% 12.46/4.67  tff(c_19107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_19103])).
% 12.46/4.67  tff(c_19109, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_19099])).
% 12.46/4.67  tff(c_16066, plain, (![B_1025, A_1026, C_1027]: (k1_xboole_0=B_1025 | k1_relset_1(A_1026, B_1025, C_1027)=A_1026 | ~v1_funct_2(C_1027, A_1026, B_1025) | ~m1_subset_1(C_1027, k1_zfmisc_1(k2_zfmisc_1(A_1026, B_1025))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.46/4.67  tff(c_16090, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_16066])).
% 12.46/4.67  tff(c_16102, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_180, c_16090])).
% 12.46/4.67  tff(c_16103, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_16102])).
% 12.46/4.67  tff(c_18794, plain, (![A_1199]: (m1_subset_1(k2_relat_1(A_1199), k1_zfmisc_1(k2_relat_1(A_1199))) | ~m1_subset_1(A_1199, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1199), k2_relat_1(A_1199)))) | ~v1_funct_1(A_1199) | ~v1_relat_1(A_1199))), inference(superposition, [status(thm), theory('equality')], [c_238, c_416])).
% 12.46/4.67  tff(c_18842, plain, (![A_1200]: (m1_subset_1(k2_relat_1(A_1200), k1_zfmisc_1(k2_relat_1(A_1200))) | ~v1_funct_1(A_1200) | ~v1_relat_1(A_1200))), inference(resolution, [status(thm)], [c_46, c_18794])).
% 12.46/4.67  tff(c_18873, plain, (![A_1201]: (r1_tarski(k2_relat_1(A_1201), k2_relat_1(A_1201)) | ~v1_funct_1(A_1201) | ~v1_relat_1(A_1201))), inference(resolution, [status(thm)], [c_18842, c_4])).
% 12.46/4.67  tff(c_19115, plain, (![A_1212]: (r1_tarski(k2_relat_1(k2_funct_1(A_1212)), k1_relat_1(A_1212)) | ~v1_funct_1(k2_funct_1(A_1212)) | ~v1_relat_1(k2_funct_1(A_1212)) | ~v2_funct_1(A_1212) | ~v1_funct_1(A_1212) | ~v1_relat_1(A_1212))), inference(superposition, [status(thm), theory('equality')], [c_16, c_18873])).
% 12.46/4.67  tff(c_19128, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16103, c_19115])).
% 12.46/4.67  tff(c_19144, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_19109, c_107, c_19128])).
% 12.46/4.67  tff(c_15971, plain, (![B_1012, A_1013]: (m1_subset_1(B_1012, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1012), A_1013))) | ~r1_tarski(k2_relat_1(B_1012), A_1013) | ~v1_funct_1(B_1012) | ~v1_relat_1(B_1012))), inference(cnfTransformation, [status(thm)], [f_133])).
% 12.46/4.67  tff(c_16004, plain, (![B_1012, A_1013]: (k2_relset_1(k1_relat_1(B_1012), A_1013, B_1012)=k2_relat_1(B_1012) | ~r1_tarski(k2_relat_1(B_1012), A_1013) | ~v1_funct_1(B_1012) | ~v1_relat_1(B_1012))), inference(resolution, [status(thm)], [c_15971, c_26])).
% 12.46/4.67  tff(c_19154, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_19144, c_16004])).
% 12.46/4.67  tff(c_19169, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_19109, c_107, c_19154])).
% 12.46/4.67  tff(c_19216, plain, (m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_19169, c_22])).
% 12.46/4.67  tff(c_19276, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(splitLeft, [status(thm)], [c_19216])).
% 12.46/4.67  tff(c_19355, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_19276])).
% 12.46/4.67  tff(c_19365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19109, c_107, c_19144, c_19355])).
% 12.46/4.67  tff(c_19367, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(splitRight, [status(thm)], [c_19216])).
% 12.46/4.67  tff(c_19420, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_19367])).
% 12.46/4.67  tff(c_19443, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_241, c_19420])).
% 12.46/4.67  tff(c_19445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_19443])).
% 12.46/4.67  tff(c_19446, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_16102])).
% 12.46/4.67  tff(c_20369, plain, (![A_1268, A_1269]: (A_1268='#skF_2' | ~v1_funct_2(A_1268, A_1269, '#skF_2') | A_1269='#skF_2' | ~r1_tarski(A_1268, k2_zfmisc_1(A_1269, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_19446, c_19446, c_19446, c_19446, c_528])).
% 12.46/4.67  tff(c_20383, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_116, c_20369])).
% 12.46/4.67  tff(c_20391, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_20383])).
% 12.46/4.67  tff(c_20392, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_20391])).
% 12.46/4.67  tff(c_9556, plain, (![B_652, A_653, C_654]: (k1_xboole_0=B_652 | k1_relset_1(A_653, B_652, C_654)=A_653 | ~v1_funct_2(C_654, A_653, B_652) | ~m1_subset_1(C_654, k1_zfmisc_1(k2_zfmisc_1(A_653, B_652))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.46/4.67  tff(c_9580, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_9556])).
% 12.46/4.67  tff(c_9592, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_180, c_9580])).
% 12.46/4.67  tff(c_9593, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_9592])).
% 12.46/4.67  tff(c_12174, plain, (![A_824]: (m1_subset_1(k2_relat_1(A_824), k1_zfmisc_1(k2_relat_1(A_824))) | ~m1_subset_1(A_824, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_824), k2_relat_1(A_824)))) | ~v1_funct_1(A_824) | ~v1_relat_1(A_824))), inference(superposition, [status(thm), theory('equality')], [c_238, c_416])).
% 12.46/4.67  tff(c_12236, plain, (![A_827]: (m1_subset_1(k2_relat_1(A_827), k1_zfmisc_1(k2_relat_1(A_827))) | ~v1_funct_1(A_827) | ~v1_relat_1(A_827))), inference(resolution, [status(thm)], [c_46, c_12174])).
% 12.46/4.67  tff(c_12267, plain, (![A_828]: (r1_tarski(k2_relat_1(A_828), k2_relat_1(A_828)) | ~v1_funct_1(A_828) | ~v1_relat_1(A_828))), inference(resolution, [status(thm)], [c_12236, c_4])).
% 12.46/4.67  tff(c_12383, plain, (![A_835]: (r1_tarski(k2_relat_1(k2_funct_1(A_835)), k1_relat_1(A_835)) | ~v1_funct_1(k2_funct_1(A_835)) | ~v1_relat_1(k2_funct_1(A_835)) | ~v2_funct_1(A_835) | ~v1_funct_1(A_835) | ~v1_relat_1(A_835))), inference(superposition, [status(thm), theory('equality')], [c_16, c_12267])).
% 12.46/4.67  tff(c_12396, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9593, c_12383])).
% 12.46/4.67  tff(c_12409, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_107, c_12396])).
% 12.46/4.67  tff(c_12410, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_12409])).
% 12.46/4.67  tff(c_12425, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_12410])).
% 12.46/4.67  tff(c_12429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_12425])).
% 12.46/4.67  tff(c_12431, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_12409])).
% 12.46/4.67  tff(c_12430, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(splitRight, [status(thm)], [c_12409])).
% 12.46/4.67  tff(c_9498, plain, (![B_645, A_646]: (m1_subset_1(B_645, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_645), A_646))) | ~r1_tarski(k2_relat_1(B_645), A_646) | ~v1_funct_1(B_645) | ~v1_relat_1(B_645))), inference(cnfTransformation, [status(thm)], [f_133])).
% 12.46/4.67  tff(c_9528, plain, (![B_645, A_646]: (k2_relset_1(k1_relat_1(B_645), A_646, B_645)=k2_relat_1(B_645) | ~r1_tarski(k2_relat_1(B_645), A_646) | ~v1_funct_1(B_645) | ~v1_relat_1(B_645))), inference(resolution, [status(thm)], [c_9498, c_26])).
% 12.46/4.67  tff(c_12437, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_12430, c_9528])).
% 12.46/4.67  tff(c_12451, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12431, c_107, c_12437])).
% 12.46/4.67  tff(c_12475, plain, (m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_12451, c_22])).
% 12.46/4.67  tff(c_12571, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(splitLeft, [status(thm)], [c_12475])).
% 12.46/4.67  tff(c_12574, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_12571])).
% 12.46/4.67  tff(c_12584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12431, c_107, c_12430, c_12574])).
% 12.46/4.67  tff(c_12586, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(splitRight, [status(thm)], [c_12475])).
% 12.46/4.67  tff(c_12647, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_12586])).
% 12.46/4.67  tff(c_12670, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_241, c_12647])).
% 12.46/4.67  tff(c_12672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_12670])).
% 12.46/4.67  tff(c_12673, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_9592])).
% 12.46/4.67  tff(c_13390, plain, (![A_884, A_885]: (A_884='#skF_2' | ~v1_funct_2(A_884, A_885, '#skF_2') | A_885='#skF_2' | ~r1_tarski(A_884, k2_zfmisc_1(A_885, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12673, c_12673, c_12673, c_12673, c_528])).
% 12.46/4.67  tff(c_13404, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_116, c_13390])).
% 12.46/4.67  tff(c_13413, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_13404])).
% 12.46/4.67  tff(c_13414, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_13413])).
% 12.46/4.67  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.46/4.67  tff(c_190, plain, (![A_61, B_62, A_63]: (k1_relset_1(A_61, B_62, A_63)=k1_relat_1(A_63) | ~r1_tarski(A_63, k2_zfmisc_1(A_61, B_62)))), inference(resolution, [status(thm)], [c_6, c_171])).
% 12.46/4.67  tff(c_200, plain, (![A_61, B_62]: (k1_relset_1(A_61, B_62, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_190])).
% 12.46/4.67  tff(c_292, plain, (![A_70, B_71, A_72]: (k2_relset_1(A_70, B_71, A_72)=k2_relat_1(A_72) | ~r1_tarski(A_72, k2_zfmisc_1(A_70, B_71)))), inference(resolution, [status(thm)], [c_6, c_227])).
% 12.46/4.67  tff(c_307, plain, (![A_70, B_71]: (k2_relset_1(A_70, B_71, k1_xboole_0)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_292])).
% 12.46/4.67  tff(c_457, plain, (![B_83, A_84]: (m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(B_83)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(superposition, [status(thm), theory('equality')], [c_307, c_416])).
% 12.46/4.67  tff(c_463, plain, (![B_83, A_84]: (m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(B_83)) | ~r1_tarski(k1_xboole_0, k2_zfmisc_1(A_84, B_83)))), inference(resolution, [status(thm)], [c_6, c_457])).
% 12.46/4.67  tff(c_469, plain, (![B_83]: (m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(B_83)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_463])).
% 12.46/4.67  tff(c_526, plain, (![A_90]: (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_funct_2(k2_relat_1(k1_xboole_0), A_90, k1_xboole_0) | k1_xboole_0=A_90)), inference(resolution, [status(thm)], [c_469, c_513])).
% 12.46/4.67  tff(c_673, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_526])).
% 12.46/4.67  tff(c_682, plain, (![B_83]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(B_83)))), inference(demodulation, [status(thm), theory('equality')], [c_673, c_469])).
% 12.46/4.67  tff(c_753, plain, (![B_107, C_108]: (k1_relset_1(k1_xboole_0, B_107, C_108)=k1_xboole_0 | ~v1_funct_2(C_108, k1_xboole_0, B_107) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_107))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.46/4.67  tff(c_757, plain, (![B_107]: (k1_relset_1(k1_xboole_0, B_107, k1_xboole_0)=k1_xboole_0 | ~v1_funct_2(k1_xboole_0, k1_xboole_0, B_107))), inference(resolution, [status(thm)], [c_682, c_753])).
% 12.46/4.67  tff(c_767, plain, (![B_107]: (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_funct_2(k1_xboole_0, k1_xboole_0, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_757])).
% 12.46/4.67  tff(c_9414, plain, (![B_107]: (~v1_funct_2(k1_xboole_0, k1_xboole_0, B_107))), inference(splitLeft, [status(thm)], [c_767])).
% 12.46/4.67  tff(c_12680, plain, (![B_107]: (~v1_funct_2('#skF_2', '#skF_2', B_107))), inference(demodulation, [status(thm), theory('equality')], [c_12673, c_12673, c_9414])).
% 12.46/4.67  tff(c_13428, plain, (![B_107]: (~v1_funct_2('#skF_1', '#skF_1', B_107))), inference(demodulation, [status(thm), theory('equality')], [c_13414, c_13414, c_12680])).
% 12.46/4.67  tff(c_12674, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_9592])).
% 12.46/4.67  tff(c_248, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_241, c_48])).
% 12.46/4.67  tff(c_254, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_248])).
% 12.46/4.67  tff(c_245, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_241, c_46])).
% 12.46/4.67  tff(c_252, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_245])).
% 12.46/4.67  tff(c_273, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_252, c_4])).
% 12.46/4.67  tff(c_13401, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relat_1('#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_273, c_13390])).
% 12.46/4.67  tff(c_13410, plain, ('#skF_2'='#skF_3' | k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_254, c_13401])).
% 12.46/4.67  tff(c_13698, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13414, c_13414, c_13410])).
% 12.46/4.67  tff(c_13699, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_12674, c_13698])).
% 12.46/4.67  tff(c_13455, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13414, c_66])).
% 12.46/4.67  tff(c_13708, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13699, c_13455])).
% 12.46/4.67  tff(c_13720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13428, c_13708])).
% 12.46/4.67  tff(c_13721, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_13413])).
% 12.46/4.67  tff(c_796, plain, (![C_111, B_112]: (v1_funct_2(C_111, k1_xboole_0, B_112) | k1_relset_1(k1_xboole_0, B_112, C_111)!=k1_xboole_0 | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_112))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.46/4.67  tff(c_800, plain, (![B_112]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_112) | k1_relset_1(k1_xboole_0, B_112, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_682, c_796])).
% 12.46/4.67  tff(c_810, plain, (![B_112]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_112) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_200, c_800])).
% 12.46/4.67  tff(c_9466, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_9414, c_810])).
% 12.46/4.67  tff(c_12679, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12673, c_12673, c_9466])).
% 12.46/4.67  tff(c_13738, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13721, c_13721, c_12679])).
% 12.46/4.67  tff(c_13035, plain, (![A_872, A_873]: (A_872='#skF_2' | ~v1_funct_2(A_872, A_873, '#skF_2') | A_873='#skF_2' | ~r1_tarski(A_872, k2_zfmisc_1(A_873, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12673, c_12673, c_12673, c_12673, c_528])).
% 12.46/4.67  tff(c_13049, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_116, c_13035])).
% 12.46/4.67  tff(c_13058, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_13049])).
% 12.46/4.67  tff(c_13059, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_13058])).
% 12.46/4.67  tff(c_13099, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13059, c_66])).
% 12.46/4.67  tff(c_13096, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13059, c_116])).
% 12.46/4.67  tff(c_13080, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13059, c_12673])).
% 12.46/4.67  tff(c_769, plain, (![B_107, A_2]: (k1_relset_1(k1_xboole_0, B_107, A_2)=k1_xboole_0 | ~v1_funct_2(A_2, k1_xboole_0, B_107) | ~r1_tarski(A_2, k2_zfmisc_1(k1_xboole_0, B_107)))), inference(resolution, [status(thm)], [c_6, c_753])).
% 12.46/4.67  tff(c_13279, plain, (![B_882, A_883]: (k1_relset_1('#skF_1', B_882, A_883)='#skF_1' | ~v1_funct_2(A_883, '#skF_1', B_882) | ~r1_tarski(A_883, k2_zfmisc_1('#skF_1', B_882)))), inference(demodulation, [status(thm), theory('equality')], [c_13080, c_13080, c_13080, c_13080, c_769])).
% 12.46/4.67  tff(c_13282, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_13096, c_13279])).
% 12.46/4.67  tff(c_13293, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13099, c_13282])).
% 12.46/4.68  tff(c_13097, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_13059, c_64])).
% 12.46/4.68  tff(c_24, plain, (![A_16, B_17, C_18]: (k1_relset_1(A_16, B_17, C_18)=k1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.46/4.68  tff(c_13318, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_13097, c_24])).
% 12.46/4.68  tff(c_13335, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13293, c_13318])).
% 12.46/4.68  tff(c_13337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12674, c_13335])).
% 12.46/4.68  tff(c_13338, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_13058])).
% 12.46/4.68  tff(c_127, plain, (![A_50, A_51, B_52]: (v1_relat_1(A_50) | ~r1_tarski(A_50, k2_zfmisc_1(A_51, B_52)))), inference(resolution, [status(thm)], [c_6, c_117])).
% 12.46/4.68  tff(c_137, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_127])).
% 12.46/4.68  tff(c_12691, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12673, c_137])).
% 12.46/4.68  tff(c_5466, plain, (![B_409, A_410, C_411]: (k1_xboole_0=B_409 | k1_relset_1(A_410, B_409, C_411)=A_410 | ~v1_funct_2(C_411, A_410, B_409) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(A_410, B_409))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.46/4.68  tff(c_5490, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_5466])).
% 12.46/4.68  tff(c_5502, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_180, c_5490])).
% 12.46/4.68  tff(c_5503, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_5502])).
% 12.46/4.68  tff(c_8029, plain, (![A_565]: (m1_subset_1(k2_relat_1(A_565), k1_zfmisc_1(k2_relat_1(A_565))) | ~m1_subset_1(A_565, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_565), k2_relat_1(A_565)))) | ~v1_funct_1(A_565) | ~v1_relat_1(A_565))), inference(superposition, [status(thm), theory('equality')], [c_238, c_416])).
% 12.46/4.68  tff(c_8077, plain, (![A_566]: (m1_subset_1(k2_relat_1(A_566), k1_zfmisc_1(k2_relat_1(A_566))) | ~v1_funct_1(A_566) | ~v1_relat_1(A_566))), inference(resolution, [status(thm)], [c_46, c_8029])).
% 12.46/4.68  tff(c_8108, plain, (![A_567]: (r1_tarski(k2_relat_1(A_567), k2_relat_1(A_567)) | ~v1_funct_1(A_567) | ~v1_relat_1(A_567))), inference(resolution, [status(thm)], [c_8077, c_4])).
% 12.46/4.68  tff(c_8249, plain, (![A_576]: (r1_tarski(k2_relat_1(k2_funct_1(A_576)), k1_relat_1(A_576)) | ~v1_funct_1(k2_funct_1(A_576)) | ~v1_relat_1(k2_funct_1(A_576)) | ~v2_funct_1(A_576) | ~v1_funct_1(A_576) | ~v1_relat_1(A_576))), inference(superposition, [status(thm), theory('equality')], [c_16, c_8108])).
% 12.46/4.68  tff(c_8262, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5503, c_8249])).
% 12.46/4.68  tff(c_8278, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_107, c_8262])).
% 12.46/4.68  tff(c_8298, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_8278])).
% 12.46/4.68  tff(c_8301, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_8298])).
% 12.46/4.68  tff(c_8305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_8301])).
% 12.46/4.68  tff(c_8307, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_8278])).
% 12.46/4.68  tff(c_8306, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(splitRight, [status(thm)], [c_8278])).
% 12.46/4.68  tff(c_5344, plain, (![B_399, A_400]: (m1_subset_1(B_399, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_399), A_400))) | ~r1_tarski(k2_relat_1(B_399), A_400) | ~v1_funct_1(B_399) | ~v1_relat_1(B_399))), inference(cnfTransformation, [status(thm)], [f_133])).
% 12.46/4.68  tff(c_5377, plain, (![B_399, A_400]: (k2_relset_1(k1_relat_1(B_399), A_400, B_399)=k2_relat_1(B_399) | ~r1_tarski(k2_relat_1(B_399), A_400) | ~v1_funct_1(B_399) | ~v1_relat_1(B_399))), inference(resolution, [status(thm)], [c_5344, c_26])).
% 12.46/4.68  tff(c_8320, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_8306, c_5377])).
% 12.46/4.68  tff(c_8334, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8307, c_107, c_8320])).
% 12.46/4.68  tff(c_8362, plain, (m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8334, c_22])).
% 12.46/4.68  tff(c_8449, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(splitLeft, [status(thm)], [c_8362])).
% 12.46/4.68  tff(c_8452, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_8449])).
% 12.46/4.68  tff(c_8462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8307, c_107, c_8306, c_8452])).
% 12.46/4.68  tff(c_8464, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(splitRight, [status(thm)], [c_8362])).
% 12.46/4.68  tff(c_8584, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_8464])).
% 12.46/4.68  tff(c_8607, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_241, c_8584])).
% 12.46/4.68  tff(c_8609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_8607])).
% 12.46/4.68  tff(c_8610, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_5502])).
% 12.46/4.68  tff(c_8979, plain, (![A_617, A_618]: (A_617='#skF_2' | ~v1_funct_2(A_617, A_618, '#skF_2') | A_618='#skF_2' | ~r1_tarski(A_617, k2_zfmisc_1(A_618, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_8610, c_8610, c_8610, c_8610, c_528])).
% 12.46/4.68  tff(c_8993, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_116, c_8979])).
% 12.46/4.68  tff(c_9001, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_8993])).
% 12.46/4.68  tff(c_9002, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_9001])).
% 12.46/4.68  tff(c_189, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_185])).
% 12.46/4.68  tff(c_982, plain, (![B_135, A_136, C_137]: (k1_xboole_0=B_135 | k1_relset_1(A_136, B_135, C_137)=A_136 | ~v1_funct_2(C_137, A_136, B_135) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_136, B_135))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.46/4.68  tff(c_1006, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_982])).
% 12.46/4.68  tff(c_1018, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_180, c_1006])).
% 12.46/4.68  tff(c_1019, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1018])).
% 12.46/4.68  tff(c_3614, plain, (![A_306]: (m1_subset_1(k2_relat_1(A_306), k1_zfmisc_1(k2_relat_1(A_306))) | ~m1_subset_1(A_306, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_306), k2_relat_1(A_306)))) | ~v1_funct_1(A_306) | ~v1_relat_1(A_306))), inference(superposition, [status(thm), theory('equality')], [c_238, c_416])).
% 12.46/4.68  tff(c_3666, plain, (![A_309]: (m1_subset_1(k2_relat_1(A_309), k1_zfmisc_1(k2_relat_1(A_309))) | ~v1_funct_1(A_309) | ~v1_relat_1(A_309))), inference(resolution, [status(thm)], [c_46, c_3614])).
% 12.46/4.68  tff(c_3697, plain, (![A_310]: (r1_tarski(k2_relat_1(A_310), k2_relat_1(A_310)) | ~v1_funct_1(A_310) | ~v1_relat_1(A_310))), inference(resolution, [status(thm)], [c_3666, c_4])).
% 12.46/4.68  tff(c_3828, plain, (![A_319]: (r1_tarski(k2_relat_1(k2_funct_1(A_319)), k1_relat_1(A_319)) | ~v1_funct_1(k2_funct_1(A_319)) | ~v1_relat_1(k2_funct_1(A_319)) | ~v2_funct_1(A_319) | ~v1_funct_1(A_319) | ~v1_relat_1(A_319))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3697])).
% 12.46/4.68  tff(c_3841, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1019, c_3828])).
% 12.46/4.68  tff(c_3854, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_107, c_3841])).
% 12.46/4.68  tff(c_3855, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3854])).
% 12.46/4.68  tff(c_3912, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_3855])).
% 12.46/4.68  tff(c_3916, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_3912])).
% 12.46/4.68  tff(c_3918, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3854])).
% 12.46/4.68  tff(c_618, plain, (![A_97, B_98, C_99, D_100]: (k7_relset_1(A_97, B_98, C_99, D_100)=k9_relat_1(C_99, D_100) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.46/4.68  tff(c_643, plain, (![D_100]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_100)=k9_relat_1('#skF_3', D_100))), inference(resolution, [status(thm)], [c_64, c_618])).
% 12.46/4.68  tff(c_863, plain, (![A_119, B_120, C_121]: (k7_relset_1(A_119, B_120, C_121, A_119)=k2_relset_1(A_119, B_120, C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.46/4.68  tff(c_878, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_863])).
% 12.46/4.68  tff(c_887, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_643, c_60, c_878])).
% 12.46/4.68  tff(c_14, plain, (![B_8, A_7]: (k10_relat_1(B_8, k9_relat_1(B_8, A_7))=A_7 | ~v2_funct_1(B_8) | ~r1_tarski(A_7, k1_relat_1(B_8)) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.46/4.68  tff(c_1038, plain, (![A_7]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_7))=A_7 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_7, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1019, c_14])).
% 12.46/4.68  tff(c_1091, plain, (![A_139]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_139))=A_139 | ~r1_tarski(A_139, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_1038])).
% 12.46/4.68  tff(c_1100, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_887, c_1091])).
% 12.46/4.68  tff(c_1134, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_1100])).
% 12.46/4.68  tff(c_2240, plain, (![A_222]: (m1_subset_1(k2_relat_1(A_222), k1_zfmisc_1(k2_relat_1(A_222))) | ~m1_subset_1(A_222, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_222), k2_relat_1(A_222)))) | ~v1_funct_1(A_222) | ~v1_relat_1(A_222))), inference(superposition, [status(thm), theory('equality')], [c_238, c_416])).
% 12.46/4.68  tff(c_2283, plain, (![A_223]: (m1_subset_1(k2_relat_1(A_223), k1_zfmisc_1(k2_relat_1(A_223))) | ~v1_funct_1(A_223) | ~v1_relat_1(A_223))), inference(resolution, [status(thm)], [c_46, c_2240])).
% 12.46/4.68  tff(c_2336, plain, (![A_226]: (r1_tarski(k2_relat_1(A_226), k2_relat_1(A_226)) | ~v1_funct_1(A_226) | ~v1_relat_1(A_226))), inference(resolution, [status(thm)], [c_2283, c_4])).
% 12.46/4.68  tff(c_2437, plain, (![A_230]: (r1_tarski(k1_relat_1(A_230), k2_relat_1(k2_funct_1(A_230))) | ~v1_funct_1(k2_funct_1(A_230)) | ~v1_relat_1(k2_funct_1(A_230)) | ~v2_funct_1(A_230) | ~v1_funct_1(A_230) | ~v1_relat_1(A_230))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2336])).
% 12.46/4.68  tff(c_2440, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1019, c_2437])).
% 12.46/4.68  tff(c_2448, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_107, c_2440])).
% 12.46/4.68  tff(c_2503, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2448])).
% 12.46/4.68  tff(c_2506, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_2503])).
% 12.46/4.68  tff(c_2510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_2506])).
% 12.46/4.68  tff(c_2511, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2448])).
% 12.46/4.68  tff(c_2515, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_2511])).
% 12.46/4.68  tff(c_2517, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_1019, c_2515])).
% 12.46/4.68  tff(c_2519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1134, c_2517])).
% 12.46/4.68  tff(c_2520, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1100])).
% 12.46/4.68  tff(c_3917, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(splitRight, [status(thm)], [c_3854])).
% 12.46/4.68  tff(c_926, plain, (![B_128, A_129]: (m1_subset_1(B_128, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_128), A_129))) | ~r1_tarski(k2_relat_1(B_128), A_129) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128))), inference(cnfTransformation, [status(thm)], [f_133])).
% 12.46/4.68  tff(c_956, plain, (![B_128, A_129]: (k2_relset_1(k1_relat_1(B_128), A_129, B_128)=k2_relat_1(B_128) | ~r1_tarski(k2_relat_1(B_128), A_129) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128))), inference(resolution, [status(thm)], [c_926, c_26])).
% 12.46/4.68  tff(c_3926, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3917, c_956])).
% 12.46/4.68  tff(c_3941, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3918, c_107, c_3926])).
% 12.46/4.68  tff(c_32, plain, (![A_26, B_27, C_28]: (k7_relset_1(A_26, B_27, C_28, A_26)=k2_relset_1(A_26, B_27, C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.46/4.68  tff(c_4008, plain, (![B_326, A_327]: (k7_relset_1(k1_relat_1(B_326), A_327, B_326, k1_relat_1(B_326))=k2_relset_1(k1_relat_1(B_326), A_327, B_326) | ~r1_tarski(k2_relat_1(B_326), A_327) | ~v1_funct_1(B_326) | ~v1_relat_1(B_326))), inference(resolution, [status(thm)], [c_926, c_32])).
% 12.46/4.68  tff(c_28, plain, (![A_22, B_23, C_24, D_25]: (k7_relset_1(A_22, B_23, C_24, D_25)=k9_relat_1(C_24, D_25) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.46/4.68  tff(c_954, plain, (![B_128, A_129, D_25]: (k7_relset_1(k1_relat_1(B_128), A_129, B_128, D_25)=k9_relat_1(B_128, D_25) | ~r1_tarski(k2_relat_1(B_128), A_129) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128))), inference(resolution, [status(thm)], [c_926, c_28])).
% 12.46/4.68  tff(c_3922, plain, (![D_25]: (k7_relset_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1', k2_funct_1('#skF_3'), D_25)=k9_relat_1(k2_funct_1('#skF_3'), D_25) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_3917, c_954])).
% 12.46/4.68  tff(c_3935, plain, (![D_25]: (k7_relset_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1', k2_funct_1('#skF_3'), D_25)=k9_relat_1(k2_funct_1('#skF_3'), D_25))), inference(demodulation, [status(thm), theory('equality')], [c_3918, c_107, c_3922])).
% 12.46/4.68  tff(c_4015, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1', k2_funct_1('#skF_3'))=k9_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4008, c_3935])).
% 12.46/4.68  tff(c_4060, plain, (k9_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3918, c_107, c_3917, c_3941, c_4015])).
% 12.46/4.68  tff(c_4090, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_4060])).
% 12.46/4.68  tff(c_4104, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_241, c_4090])).
% 12.46/4.68  tff(c_12, plain, (![B_6, A_5]: (k9_relat_1(k2_funct_1(B_6), A_5)=k10_relat_1(B_6, A_5) | ~v2_funct_1(B_6) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.46/4.68  tff(c_4108, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4104, c_12])).
% 12.46/4.68  tff(c_4115, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_2520, c_4108])).
% 12.46/4.68  tff(c_208, plain, (![A_66]: (m1_subset_1(A_66, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_66), k2_relat_1(A_66)))) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.46/4.68  tff(c_226, plain, (![A_66]: (r1_tarski(A_66, k2_zfmisc_1(k1_relat_1(A_66), k2_relat_1(A_66))) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_208, c_4])).
% 12.46/4.68  tff(c_4181, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4115, c_226])).
% 12.46/4.68  tff(c_4235, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3918, c_107, c_4181])).
% 12.46/4.68  tff(c_4420, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_4235])).
% 12.46/4.68  tff(c_4440, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_241, c_4420])).
% 12.46/4.68  tff(c_4442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_4440])).
% 12.46/4.68  tff(c_4443, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1018])).
% 12.46/4.68  tff(c_4813, plain, (![A_366, A_367]: (A_366='#skF_2' | ~v1_funct_2(A_366, A_367, '#skF_2') | A_367='#skF_2' | ~r1_tarski(A_366, k2_zfmisc_1(A_367, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4443, c_4443, c_4443, c_4443, c_528])).
% 12.46/4.68  tff(c_4827, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_116, c_4813])).
% 12.46/4.68  tff(c_4836, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4827])).
% 12.46/4.68  tff(c_4851, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_4836])).
% 12.46/4.68  tff(c_814, plain, (![B_107]: (~v1_funct_2(k1_xboole_0, k1_xboole_0, B_107))), inference(splitLeft, [status(thm)], [c_767])).
% 12.46/4.68  tff(c_4450, plain, (![B_107]: (~v1_funct_2('#skF_2', '#skF_2', B_107))), inference(demodulation, [status(thm), theory('equality')], [c_4443, c_4443, c_814])).
% 12.46/4.68  tff(c_4863, plain, (![B_107]: (~v1_funct_2('#skF_1', '#skF_1', B_107))), inference(demodulation, [status(thm), theory('equality')], [c_4851, c_4851, c_4450])).
% 12.46/4.68  tff(c_4444, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_1018])).
% 12.46/4.68  tff(c_4824, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relat_1('#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_273, c_4813])).
% 12.46/4.68  tff(c_4833, plain, ('#skF_2'='#skF_3' | k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_254, c_4824])).
% 12.46/4.68  tff(c_5108, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4851, c_4851, c_4833])).
% 12.46/4.68  tff(c_5109, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_4444, c_5108])).
% 12.46/4.68  tff(c_4890, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4851, c_66])).
% 12.46/4.68  tff(c_5116, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5109, c_4890])).
% 12.46/4.68  tff(c_5127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4863, c_5116])).
% 12.46/4.68  tff(c_5128, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_4836])).
% 12.46/4.68  tff(c_704, plain, (v1_funct_2(k1_xboole_0, k1_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_673, c_48])).
% 12.46/4.68  tff(c_716, plain, (v1_funct_2(k1_xboole_0, k1_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_137, c_704])).
% 12.46/4.68  tff(c_813, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_716])).
% 12.46/4.68  tff(c_4451, plain, (~v1_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4443, c_813])).
% 12.46/4.68  tff(c_5147, plain, (~v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5128, c_4451])).
% 12.46/4.68  tff(c_5171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_5147])).
% 12.46/4.68  tff(c_5172, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_767])).
% 12.46/4.68  tff(c_8618, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8610, c_8610, c_5172])).
% 12.46/4.68  tff(c_9030, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9002, c_9002, c_8618])).
% 12.46/4.68  tff(c_8611, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_5502])).
% 12.46/4.68  tff(c_8990, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relat_1('#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_273, c_8979])).
% 12.46/4.68  tff(c_8998, plain, ('#skF_2'='#skF_3' | k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_254, c_8990])).
% 12.46/4.68  tff(c_9316, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9002, c_9002, c_8998])).
% 12.46/4.68  tff(c_9317, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_8611, c_9316])).
% 12.46/4.68  tff(c_9326, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9317, c_8611])).
% 12.46/4.68  tff(c_9339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9030, c_9326])).
% 12.46/4.68  tff(c_9340, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_9001])).
% 12.46/4.68  tff(c_8619, plain, (~v1_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8610, c_813])).
% 12.46/4.68  tff(c_9358, plain, (~v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9340, c_8619])).
% 12.46/4.68  tff(c_9382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_9358])).
% 12.46/4.68  tff(c_9384, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_716])).
% 12.46/4.68  tff(c_12682, plain, (v1_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12673, c_9384])).
% 12.46/4.68  tff(c_638, plain, (![A_97, B_98, D_100]: (k7_relset_1(A_97, B_98, k2_relat_1(k1_xboole_0), D_100)=k9_relat_1(k2_relat_1(k1_xboole_0), D_100))), inference(resolution, [status(thm)], [c_469, c_618])).
% 12.46/4.68  tff(c_9474, plain, (![A_641, B_642, D_643]: (k7_relset_1(A_641, B_642, k1_xboole_0, D_643)=k9_relat_1(k1_xboole_0, D_643))), inference(demodulation, [status(thm), theory('equality')], [c_673, c_673, c_638])).
% 12.46/4.68  tff(c_471, plain, (![B_85]: (m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(B_85)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_463])).
% 12.46/4.68  tff(c_487, plain, (![A_19, B_20]: (k2_relset_1(A_19, B_20, k2_relat_1(k1_xboole_0))=k2_relat_1(k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_471, c_26])).
% 12.46/4.68  tff(c_678, plain, (![A_19, B_20]: (k2_relset_1(A_19, B_20, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_673, c_673, c_673, c_487])).
% 12.46/4.68  tff(c_9422, plain, (![A_634, B_635, C_636]: (k7_relset_1(A_634, B_635, C_636, A_634)=k2_relset_1(A_634, B_635, C_636) | ~m1_subset_1(C_636, k1_zfmisc_1(k2_zfmisc_1(A_634, B_635))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.46/4.68  tff(c_9425, plain, (![A_634, B_635]: (k7_relset_1(A_634, B_635, k1_xboole_0, A_634)=k2_relset_1(A_634, B_635, k1_xboole_0))), inference(resolution, [status(thm)], [c_682, c_9422])).
% 12.46/4.68  tff(c_9439, plain, (![A_634, B_635]: (k7_relset_1(A_634, B_635, k1_xboole_0, A_634)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_678, c_9425])).
% 12.46/4.68  tff(c_9480, plain, (![D_643]: (k9_relat_1(k1_xboole_0, D_643)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9474, c_9439])).
% 12.46/4.68  tff(c_12677, plain, (![D_643]: (k9_relat_1('#skF_2', D_643)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12673, c_12673, c_9480])).
% 12.46/4.68  tff(c_9543, plain, (![B_650, A_651]: (k10_relat_1(B_650, k9_relat_1(B_650, A_651))=A_651 | ~v2_funct_1(B_650) | ~r1_tarski(A_651, k1_relat_1(B_650)) | ~v1_funct_1(B_650) | ~v1_relat_1(B_650))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.46/4.68  tff(c_9549, plain, (![B_650]: (k10_relat_1(B_650, k9_relat_1(B_650, k1_xboole_0))=k1_xboole_0 | ~v2_funct_1(B_650) | ~v1_funct_1(B_650) | ~v1_relat_1(B_650))), inference(resolution, [status(thm)], [c_2, c_9543])).
% 12.46/4.68  tff(c_13014, plain, (![B_871]: (k10_relat_1(B_871, k9_relat_1(B_871, '#skF_2'))='#skF_2' | ~v2_funct_1(B_871) | ~v1_funct_1(B_871) | ~v1_relat_1(B_871))), inference(demodulation, [status(thm), theory('equality')], [c_12673, c_12673, c_9549])).
% 12.46/4.68  tff(c_13024, plain, (k10_relat_1('#skF_2', '#skF_2')='#skF_2' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12677, c_13014])).
% 12.46/4.68  tff(c_13032, plain, (k10_relat_1('#skF_2', '#skF_2')='#skF_2' | ~v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12691, c_12682, c_13024])).
% 12.46/4.68  tff(c_13033, plain, (~v2_funct_1('#skF_2')), inference(splitLeft, [status(thm)], [c_13032])).
% 12.46/4.68  tff(c_13341, plain, (~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13338, c_13033])).
% 12.46/4.68  tff(c_13382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_13341])).
% 12.46/4.68  tff(c_13383, plain, (k10_relat_1('#skF_2', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_13032])).
% 12.46/4.68  tff(c_13724, plain, (k10_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13721, c_13721, c_13721, c_13383])).
% 12.46/4.68  tff(c_13756, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13721, c_241])).
% 12.46/4.68  tff(c_15132, plain, (![A_1000]: (v1_funct_2(k2_funct_1(A_1000), k2_relat_1(A_1000), k2_relat_1(k2_funct_1(A_1000))) | ~v1_funct_1(k2_funct_1(A_1000)) | ~v1_relat_1(k2_funct_1(A_1000)) | ~v2_funct_1(A_1000) | ~v1_funct_1(A_1000) | ~v1_relat_1(A_1000))), inference(superposition, [status(thm), theory('equality')], [c_151, c_48])).
% 12.46/4.68  tff(c_15135, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13756, c_15132])).
% 12.46/4.68  tff(c_15143, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_107, c_15135])).
% 12.46/4.68  tff(c_15144, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_15143])).
% 12.46/4.68  tff(c_15147, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_15144])).
% 12.46/4.68  tff(c_15151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_15147])).
% 12.46/4.68  tff(c_15153, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_15143])).
% 12.46/4.68  tff(c_15152, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_15143])).
% 12.46/4.68  tff(c_15156, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_15152])).
% 12.46/4.68  tff(c_15158, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_15156])).
% 12.46/4.68  tff(c_324, plain, (![A_77]: (r1_tarski(A_77, k2_zfmisc_1(k1_relat_1(A_77), k2_relat_1(A_77))) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(resolution, [status(thm)], [c_208, c_4])).
% 12.46/4.68  tff(c_15159, plain, (![A_1001]: (r1_tarski(k2_funct_1(A_1001), k2_zfmisc_1(k2_relat_1(A_1001), k2_relat_1(k2_funct_1(A_1001)))) | ~v1_funct_1(k2_funct_1(A_1001)) | ~v1_relat_1(k2_funct_1(A_1001)) | ~v2_funct_1(A_1001) | ~v1_funct_1(A_1001) | ~v1_relat_1(A_1001))), inference(superposition, [status(thm), theory('equality')], [c_18, c_324])).
% 12.46/4.68  tff(c_15183, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13756, c_15159])).
% 12.46/4.68  tff(c_15199, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_15153, c_107, c_15183])).
% 12.46/4.68  tff(c_15229, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', k1_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_15199])).
% 12.46/4.68  tff(c_15248, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_15229])).
% 12.46/4.68  tff(c_13744, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13721, c_12673])).
% 12.46/4.68  tff(c_13965, plain, (![B_107, A_2]: (k1_relset_1('#skF_3', B_107, A_2)='#skF_3' | ~v1_funct_2(A_2, '#skF_3', B_107) | ~r1_tarski(A_2, k2_zfmisc_1('#skF_3', B_107)))), inference(demodulation, [status(thm), theory('equality')], [c_13744, c_13744, c_13744, c_13744, c_769])).
% 12.46/4.68  tff(c_15312, plain, (k1_relset_1('#skF_3', k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_15248, c_13965])).
% 12.46/4.68  tff(c_15337, plain, (k1_relset_1('#skF_3', k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15158, c_15312])).
% 12.46/4.68  tff(c_15249, plain, (![A_1002]: (m1_subset_1(k2_funct_1(A_1002), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1002), k2_relat_1(k2_funct_1(A_1002))))) | ~v1_funct_1(k2_funct_1(A_1002)) | ~v1_relat_1(k2_funct_1(A_1002)) | ~v2_funct_1(A_1002) | ~v1_funct_1(A_1002) | ~v1_relat_1(A_1002))), inference(superposition, [status(thm), theory('equality')], [c_18, c_208])).
% 12.46/4.68  tff(c_15278, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13756, c_15249])).
% 12.46/4.68  tff(c_15296, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_15153, c_107, c_15278])).
% 12.46/4.68  tff(c_15382, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_15296])).
% 12.46/4.68  tff(c_15404, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_15382])).
% 12.46/4.68  tff(c_15440, plain, (k1_relset_1('#skF_3', k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_15404, c_24])).
% 12.46/4.68  tff(c_15468, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15337, c_15440])).
% 12.46/4.68  tff(c_641, plain, (![A_32, D_100]: (k7_relset_1(k1_relat_1(A_32), k2_relat_1(A_32), A_32, D_100)=k9_relat_1(A_32, D_100) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(resolution, [status(thm)], [c_46, c_618])).
% 12.46/4.68  tff(c_14705, plain, (![A_977]: (k7_relset_1(k1_relat_1(A_977), k2_relat_1(A_977), A_977, k1_relat_1(A_977))=k2_relset_1(k1_relat_1(A_977), k2_relat_1(A_977), A_977) | ~v1_funct_1(A_977) | ~v1_relat_1(A_977))), inference(resolution, [status(thm)], [c_46, c_9422])).
% 12.46/4.68  tff(c_14855, plain, (![A_986]: (k2_relset_1(k1_relat_1(A_986), k2_relat_1(A_986), A_986)=k9_relat_1(A_986, k1_relat_1(A_986)) | ~v1_funct_1(A_986) | ~v1_relat_1(A_986) | ~v1_funct_1(A_986) | ~v1_relat_1(A_986))), inference(superposition, [status(thm), theory('equality')], [c_641, c_14705])).
% 12.46/4.68  tff(c_14877, plain, (![A_986]: (k9_relat_1(A_986, k1_relat_1(A_986))=k2_relat_1(A_986) | ~v1_funct_1(A_986) | ~v1_relat_1(A_986) | ~v1_funct_1(A_986) | ~v1_relat_1(A_986) | ~v1_funct_1(A_986) | ~v1_relat_1(A_986))), inference(superposition, [status(thm), theory('equality')], [c_14855, c_238])).
% 12.46/4.68  tff(c_15503, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_15468, c_14877])).
% 12.46/4.68  tff(c_15581, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15153, c_107, c_15153, c_107, c_15153, c_107, c_15503])).
% 12.46/4.68  tff(c_15627, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15581, c_12])).
% 12.46/4.68  tff(c_15636, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_13724, c_15627])).
% 12.46/4.68  tff(c_15790, plain, (k1_relat_1('#skF_3')='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15636, c_16])).
% 12.46/4.68  tff(c_15862, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_15790])).
% 12.46/4.68  tff(c_15864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13738, c_15862])).
% 12.46/4.68  tff(c_15865, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_767])).
% 12.46/4.68  tff(c_19454, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_19446, c_19446, c_15865])).
% 12.46/4.68  tff(c_20407, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20392, c_20392, c_19454])).
% 12.46/4.68  tff(c_19447, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_16102])).
% 12.46/4.68  tff(c_20380, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relat_1('#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_273, c_20369])).
% 12.46/4.68  tff(c_20388, plain, ('#skF_2'='#skF_3' | k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_254, c_20380])).
% 12.46/4.68  tff(c_20729, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20392, c_20392, c_20388])).
% 12.46/4.68  tff(c_20730, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_19447, c_20729])).
% 12.46/4.68  tff(c_20739, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20730, c_19447])).
% 12.46/4.68  tff(c_20753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20407, c_20739])).
% 12.46/4.68  tff(c_20754, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_20391])).
% 12.46/4.68  tff(c_19459, plain, (![B_83]: (m1_subset_1('#skF_2', k1_zfmisc_1(B_83)))), inference(demodulation, [status(thm), theory('equality')], [c_19446, c_682])).
% 12.46/4.68  tff(c_20768, plain, (![B_83]: (m1_subset_1('#skF_3', k1_zfmisc_1(B_83)))), inference(demodulation, [status(thm), theory('equality')], [c_20754, c_19459])).
% 12.46/4.68  tff(c_20788, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20754, c_241])).
% 12.46/4.68  tff(c_22166, plain, (![A_1382]: (v1_funct_2(k2_funct_1(A_1382), k2_relat_1(A_1382), k2_relat_1(k2_funct_1(A_1382))) | ~v1_funct_1(k2_funct_1(A_1382)) | ~v1_relat_1(k2_funct_1(A_1382)) | ~v2_funct_1(A_1382) | ~v1_funct_1(A_1382) | ~v1_relat_1(A_1382))), inference(superposition, [status(thm), theory('equality')], [c_151, c_48])).
% 12.46/4.68  tff(c_22169, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20788, c_22166])).
% 12.46/4.68  tff(c_22177, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_107, c_22169])).
% 12.46/4.68  tff(c_22178, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_22177])).
% 12.46/4.68  tff(c_22181, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_22178])).
% 12.46/4.68  tff(c_22185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_22181])).
% 12.46/4.68  tff(c_22187, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_22177])).
% 12.46/4.68  tff(c_19464, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_19446, c_2])).
% 12.46/4.68  tff(c_20772, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_20754, c_19464])).
% 12.46/4.68  tff(c_20770, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20754, c_20754, c_19454])).
% 12.46/4.68  tff(c_21971, plain, (![A_1375]: (m1_subset_1(k2_relat_1(A_1375), k1_zfmisc_1(k2_relat_1(A_1375))) | ~m1_subset_1(A_1375, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1375), k2_relat_1(A_1375)))) | ~v1_funct_1(A_1375) | ~v1_relat_1(A_1375))), inference(superposition, [status(thm), theory('equality')], [c_238, c_416])).
% 12.46/4.68  tff(c_22009, plain, (![A_1376]: (m1_subset_1(k2_relat_1(A_1376), k1_zfmisc_1(k2_relat_1(A_1376))) | ~v1_funct_1(A_1376) | ~v1_relat_1(A_1376))), inference(resolution, [status(thm)], [c_46, c_21971])).
% 12.46/4.68  tff(c_22030, plain, (![A_1377]: (r1_tarski(k2_relat_1(A_1377), k2_relat_1(A_1377)) | ~v1_funct_1(A_1377) | ~v1_relat_1(A_1377))), inference(resolution, [status(thm)], [c_22009, c_4])).
% 12.46/4.68  tff(c_22205, plain, (![A_1384]: (r1_tarski(k2_relat_1(k2_funct_1(A_1384)), k1_relat_1(A_1384)) | ~v1_funct_1(k2_funct_1(A_1384)) | ~v1_relat_1(k2_funct_1(A_1384)) | ~v2_funct_1(A_1384) | ~v1_funct_1(A_1384) | ~v1_relat_1(A_1384))), inference(superposition, [status(thm), theory('equality')], [c_16, c_22030])).
% 12.46/4.68  tff(c_22218, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20770, c_22205])).
% 12.46/4.68  tff(c_22231, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_22187, c_107, c_22218])).
% 12.46/4.68  tff(c_19841, plain, (![A_1246, A_1247]: (A_1246='#skF_2' | ~v1_funct_2(A_1246, A_1247, '#skF_2') | A_1247='#skF_2' | ~r1_tarski(A_1246, k2_zfmisc_1(A_1247, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_19446, c_19446, c_19446, c_19446, c_528])).
% 12.46/4.68  tff(c_19855, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_116, c_19841])).
% 12.46/4.68  tff(c_19863, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_19855])).
% 12.46/4.68  tff(c_19864, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_19863])).
% 12.46/4.68  tff(c_19877, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_19864, c_19864, c_19454])).
% 12.46/4.68  tff(c_19852, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relat_1('#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_273, c_19841])).
% 12.46/4.68  tff(c_19860, plain, ('#skF_2'='#skF_3' | k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_254, c_19852])).
% 12.46/4.68  tff(c_20181, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_19864, c_19864, c_19860])).
% 12.46/4.68  tff(c_20182, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_19447, c_20181])).
% 12.46/4.68  tff(c_20191, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20182, c_19447])).
% 12.46/4.68  tff(c_20205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19877, c_20191])).
% 12.46/4.68  tff(c_20206, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_19863])).
% 12.46/4.68  tff(c_19463, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19446, c_137])).
% 12.46/4.68  tff(c_19455, plain, (v1_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19446, c_9384])).
% 12.46/4.68  tff(c_16018, plain, (![A_1016, B_1017, D_1018]: (k7_relset_1(A_1016, B_1017, k1_xboole_0, D_1018)=k9_relat_1(k1_xboole_0, D_1018))), inference(demodulation, [status(thm), theory('equality')], [c_673, c_673, c_638])).
% 12.46/4.68  tff(c_15931, plain, (![A_1007, B_1008, C_1009]: (k7_relset_1(A_1007, B_1008, C_1009, A_1007)=k2_relset_1(A_1007, B_1008, C_1009) | ~m1_subset_1(C_1009, k1_zfmisc_1(k2_zfmisc_1(A_1007, B_1008))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.46/4.68  tff(c_15934, plain, (![A_1007, B_1008]: (k7_relset_1(A_1007, B_1008, k1_xboole_0, A_1007)=k2_relset_1(A_1007, B_1008, k1_xboole_0))), inference(resolution, [status(thm)], [c_682, c_15931])).
% 12.46/4.68  tff(c_15948, plain, (![A_1007, B_1008]: (k7_relset_1(A_1007, B_1008, k1_xboole_0, A_1007)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_678, c_15934])).
% 12.46/4.68  tff(c_16024, plain, (![D_1018]: (k9_relat_1(k1_xboole_0, D_1018)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16018, c_15948])).
% 12.46/4.68  tff(c_19450, plain, (![D_1018]: (k9_relat_1('#skF_2', D_1018)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19446, c_19446, c_16024])).
% 12.46/4.68  tff(c_16050, plain, (![B_1023, A_1024]: (k10_relat_1(B_1023, k9_relat_1(B_1023, A_1024))=A_1024 | ~v2_funct_1(B_1023) | ~r1_tarski(A_1024, k1_relat_1(B_1023)) | ~v1_funct_1(B_1023) | ~v1_relat_1(B_1023))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.46/4.68  tff(c_16060, plain, (![B_1023]: (k10_relat_1(B_1023, k9_relat_1(B_1023, k1_xboole_0))=k1_xboole_0 | ~v2_funct_1(B_1023) | ~v1_funct_1(B_1023) | ~v1_relat_1(B_1023))), inference(resolution, [status(thm)], [c_2, c_16050])).
% 12.46/4.68  tff(c_19707, plain, (![B_1235]: (k10_relat_1(B_1235, k9_relat_1(B_1235, '#skF_2'))='#skF_2' | ~v2_funct_1(B_1235) | ~v1_funct_1(B_1235) | ~v1_relat_1(B_1235))), inference(demodulation, [status(thm), theory('equality')], [c_19446, c_19446, c_16060])).
% 12.46/4.68  tff(c_19717, plain, (k10_relat_1('#skF_2', '#skF_2')='#skF_2' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_19450, c_19707])).
% 12.46/4.68  tff(c_19725, plain, (k10_relat_1('#skF_2', '#skF_2')='#skF_2' | ~v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19463, c_19455, c_19717])).
% 12.46/4.68  tff(c_19739, plain, (~v2_funct_1('#skF_2')), inference(splitLeft, [status(thm)], [c_19725])).
% 12.46/4.68  tff(c_20210, plain, (~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20206, c_19739])).
% 12.46/4.68  tff(c_20248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_20210])).
% 12.46/4.68  tff(c_20250, plain, (v2_funct_1('#skF_2')), inference(splitRight, [status(thm)], [c_19725])).
% 12.46/4.68  tff(c_20249, plain, (k10_relat_1('#skF_2', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_19725])).
% 12.46/4.68  tff(c_16052, plain, (![A_1024]: (k10_relat_1(k1_xboole_0, k9_relat_1(k1_xboole_0, A_1024))=A_1024 | ~v2_funct_1(k1_xboole_0) | ~r1_tarski(A_1024, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_15865, c_16050])).
% 12.46/4.68  tff(c_16059, plain, (![A_1024]: (k10_relat_1(k1_xboole_0, k1_xboole_0)=A_1024 | ~v2_funct_1(k1_xboole_0) | ~r1_tarski(A_1024, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_9384, c_16024, c_16052])).
% 12.46/4.68  tff(c_20313, plain, (![A_1024]: (A_1024='#skF_2' | ~r1_tarski(A_1024, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_19446, c_20250, c_19446, c_20249, c_19446, c_19446, c_16059])).
% 12.46/4.68  tff(c_20757, plain, (![A_1024]: (A_1024='#skF_3' | ~r1_tarski(A_1024, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20754, c_20754, c_20313])).
% 12.46/4.68  tff(c_22269, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_22231, c_20757])).
% 12.46/4.68  tff(c_54, plain, (![B_34, A_33]: (v1_funct_2(B_34, k1_relat_1(B_34), A_33) | ~r1_tarski(k2_relat_1(B_34), A_33) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_133])).
% 12.46/4.68  tff(c_20776, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20754, c_19446])).
% 12.46/4.68  tff(c_36, plain, (![C_31, A_29]: (k1_xboole_0=C_31 | ~v1_funct_2(C_31, A_29, k1_xboole_0) | k1_xboole_0=A_29 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.46/4.68  tff(c_16003, plain, (![B_1012]: (k1_xboole_0=B_1012 | ~v1_funct_2(B_1012, k1_relat_1(B_1012), k1_xboole_0) | k1_relat_1(B_1012)=k1_xboole_0 | ~r1_tarski(k2_relat_1(B_1012), k1_xboole_0) | ~v1_funct_1(B_1012) | ~v1_relat_1(B_1012))), inference(resolution, [status(thm)], [c_15971, c_36])).
% 12.46/4.68  tff(c_21800, plain, (![B_1365]: (B_1365='#skF_3' | ~v1_funct_2(B_1365, k1_relat_1(B_1365), '#skF_3') | k1_relat_1(B_1365)='#skF_3' | ~r1_tarski(k2_relat_1(B_1365), '#skF_3') | ~v1_funct_1(B_1365) | ~v1_relat_1(B_1365))), inference(demodulation, [status(thm), theory('equality')], [c_20776, c_20776, c_20776, c_20776, c_16003])).
% 12.46/4.68  tff(c_21830, plain, (![B_34]: (B_34='#skF_3' | k1_relat_1(B_34)='#skF_3' | ~r1_tarski(k2_relat_1(B_34), '#skF_3') | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_54, c_21800])).
% 12.46/4.68  tff(c_22236, plain, (k2_funct_1('#skF_3')='#skF_3' | k1_relat_1(k2_funct_1('#skF_3'))='#skF_3' | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_22231, c_21830])).
% 12.46/4.68  tff(c_22256, plain, (k2_funct_1('#skF_3')='#skF_3' | k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22187, c_107, c_22236])).
% 12.46/4.68  tff(c_22432, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(splitLeft, [status(thm)], [c_22256])).
% 12.46/4.68  tff(c_16007, plain, (![B_1012, A_1013]: (r1_tarski(B_1012, k2_zfmisc_1(k1_relat_1(B_1012), A_1013)) | ~r1_tarski(k2_relat_1(B_1012), A_1013) | ~v1_funct_1(B_1012) | ~v1_relat_1(B_1012))), inference(resolution, [status(thm)], [c_15971, c_4])).
% 12.46/4.68  tff(c_22556, plain, (![A_1013]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', A_1013)) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1013) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_22432, c_16007])).
% 12.46/4.68  tff(c_22616, plain, (![A_1013]: (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', A_1013)))), inference(demodulation, [status(thm), theory('equality')], [c_22187, c_107, c_20772, c_22269, c_22556])).
% 12.46/4.68  tff(c_20789, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20754, c_189])).
% 12.46/4.68  tff(c_22663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22616, c_20789])).
% 12.46/4.68  tff(c_22664, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_22256])).
% 12.46/4.68  tff(c_20790, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20754, c_185])).
% 12.46/4.68  tff(c_22670, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22664, c_20790])).
% 12.46/4.68  tff(c_22679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20768, c_22670])).
% 12.46/4.68  tff(c_22681, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_526])).
% 12.46/4.68  tff(c_27465, plain, (k2_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_27447, c_27447, c_22681])).
% 12.46/4.68  tff(c_27997, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_27975, c_27975, c_27465])).
% 12.46/4.68  tff(c_27448, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_23111])).
% 12.46/4.68  tff(c_27958, plain, ('#skF_2'='#skF_3' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relat_1('#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_273, c_27935])).
% 12.46/4.68  tff(c_27971, plain, ('#skF_2'='#skF_3' | k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_254, c_27958])).
% 12.46/4.68  tff(c_28180, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_27975, c_27975, c_27971])).
% 12.46/4.68  tff(c_28181, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_27448, c_28180])).
% 12.46/4.68  tff(c_28014, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_27975, c_241])).
% 12.46/4.68  tff(c_28187, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28181, c_28014])).
% 12.46/4.68  tff(c_28196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27997, c_28187])).
% 12.46/4.68  tff(c_28197, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_27974])).
% 12.46/4.68  tff(c_28237, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28197, c_241])).
% 12.46/4.68  tff(c_28220, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28197, c_28197, c_27465])).
% 12.46/4.68  tff(c_28306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28237, c_28220])).
% 12.46/4.68  tff(c_28307, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_106])).
% 12.46/4.68  tff(c_28308, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_106])).
% 12.46/4.68  tff(c_20, plain, (![C_12, A_10, B_11]: (v1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.46/4.68  tff(c_28319, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_28308, c_20])).
% 12.46/4.68  tff(c_28387, plain, (![A_1729, B_1730, C_1731]: (k2_relset_1(A_1729, B_1730, C_1731)=k2_relat_1(C_1731) | ~m1_subset_1(C_1731, k1_zfmisc_1(k2_zfmisc_1(A_1729, B_1730))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.46/4.68  tff(c_28400, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_28387])).
% 12.46/4.68  tff(c_28405, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_28400])).
% 12.46/4.68  tff(c_28318, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_28308, c_24])).
% 12.46/4.68  tff(c_29156, plain, (![B_1790, C_1791, A_1792]: (k1_xboole_0=B_1790 | v1_funct_2(C_1791, A_1792, B_1790) | k1_relset_1(A_1792, B_1790, C_1791)!=A_1792 | ~m1_subset_1(C_1791, k1_zfmisc_1(k2_zfmisc_1(A_1792, B_1790))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.46/4.68  tff(c_29176, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_28308, c_29156])).
% 12.46/4.68  tff(c_29193, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28318, c_29176])).
% 12.46/4.68  tff(c_29194, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_28307, c_29193])).
% 12.46/4.68  tff(c_29198, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_29194])).
% 12.46/4.68  tff(c_29201, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_29198])).
% 12.46/4.68  tff(c_29204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_28405, c_29201])).
% 12.46/4.68  tff(c_29206, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_29194])).
% 12.46/4.68  tff(c_29205, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_29194])).
% 12.46/4.68  tff(c_44, plain, (![B_30, A_29, C_31]: (k1_xboole_0=B_30 | k1_relset_1(A_29, B_30, C_31)=A_29 | ~v1_funct_2(C_31, A_29, B_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.46/4.68  tff(c_29314, plain, (![B_1794, A_1795, C_1796]: (B_1794='#skF_1' | k1_relset_1(A_1795, B_1794, C_1796)=A_1795 | ~v1_funct_2(C_1796, A_1795, B_1794) | ~m1_subset_1(C_1796, k1_zfmisc_1(k2_zfmisc_1(A_1795, B_1794))))), inference(demodulation, [status(thm), theory('equality')], [c_29205, c_44])).
% 12.46/4.68  tff(c_29337, plain, ('#skF_2'='#skF_1' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_29314])).
% 12.46/4.68  tff(c_29348, plain, ('#skF_2'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_180, c_29337])).
% 12.46/4.68  tff(c_29397, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_29348])).
% 12.46/4.68  tff(c_28685, plain, (![A_1755, B_1756, C_1757, D_1758]: (k7_relset_1(A_1755, B_1756, C_1757, D_1758)=k9_relat_1(C_1757, D_1758) | ~m1_subset_1(C_1757, k1_zfmisc_1(k2_zfmisc_1(A_1755, B_1756))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.46/4.68  tff(c_28711, plain, (![D_1758]: (k7_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'), D_1758)=k9_relat_1(k2_funct_1('#skF_3'), D_1758))), inference(resolution, [status(thm)], [c_28308, c_28685])).
% 12.46/4.68  tff(c_28402, plain, (k2_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_28308, c_28387])).
% 12.46/4.68  tff(c_28981, plain, (![A_1781, B_1782, C_1783]: (k7_relset_1(A_1781, B_1782, C_1783, A_1781)=k2_relset_1(A_1781, B_1782, C_1783) | ~m1_subset_1(C_1783, k1_zfmisc_1(k2_zfmisc_1(A_1781, B_1782))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.46/4.68  tff(c_28995, plain, (k7_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'), '#skF_2')=k2_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_28308, c_28981])).
% 12.46/4.68  tff(c_29009, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28711, c_28402, c_28995])).
% 12.46/4.68  tff(c_29039, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29009, c_12])).
% 12.46/4.68  tff(c_29046, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_29039])).
% 12.46/4.68  tff(c_29070, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29046, c_16])).
% 12.46/4.68  tff(c_29084, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_29070])).
% 12.46/4.68  tff(c_29091, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_29084, c_29046])).
% 12.46/4.68  tff(c_29399, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_29397, c_29091])).
% 12.46/4.68  tff(c_29467, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_29399, c_48])).
% 12.46/4.68  tff(c_29480, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28319, c_107, c_29206, c_29467])).
% 12.46/4.68  tff(c_29482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28307, c_29480])).
% 12.46/4.68  tff(c_29484, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_29348])).
% 12.46/4.68  tff(c_29483, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_29348])).
% 12.46/4.68  tff(c_29488, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_29483, c_29084])).
% 12.46/4.68  tff(c_28713, plain, (![D_1758]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_1758)=k9_relat_1('#skF_3', D_1758))), inference(resolution, [status(thm)], [c_64, c_28685])).
% 12.46/4.68  tff(c_29000, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_28981])).
% 12.46/4.68  tff(c_29012, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28713, c_60, c_29000])).
% 12.46/4.68  tff(c_29490, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_29483, c_29012])).
% 12.46/4.68  tff(c_29050, plain, (![B_1788, A_1789]: (k10_relat_1(B_1788, k9_relat_1(B_1788, A_1789))=A_1789 | ~v2_funct_1(B_1788) | ~r1_tarski(A_1789, k1_relat_1(B_1788)) | ~v1_funct_1(B_1788) | ~v1_relat_1(B_1788))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.46/4.68  tff(c_29056, plain, (![B_1788]: (k10_relat_1(B_1788, k9_relat_1(B_1788, k1_xboole_0))=k1_xboole_0 | ~v2_funct_1(B_1788) | ~v1_funct_1(B_1788) | ~v1_relat_1(B_1788))), inference(resolution, [status(thm)], [c_2, c_29050])).
% 12.46/4.68  tff(c_29922, plain, (![B_1810]: (k10_relat_1(B_1810, k9_relat_1(B_1810, '#skF_1'))='#skF_1' | ~v2_funct_1(B_1810) | ~v1_funct_1(B_1810) | ~v1_relat_1(B_1810))), inference(demodulation, [status(thm), theory('equality')], [c_29205, c_29205, c_29056])).
% 12.46/4.68  tff(c_29934, plain, (k10_relat_1('#skF_3', '#skF_1')='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29490, c_29922])).
% 12.46/4.68  tff(c_29948, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_68, c_62, c_29488, c_29934])).
% 12.46/4.68  tff(c_29950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29484, c_29948])).
% 12.46/4.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.46/4.68  
% 12.46/4.68  Inference rules
% 12.46/4.68  ----------------------
% 12.46/4.68  #Ref     : 0
% 12.46/4.68  #Sup     : 6313
% 12.46/4.68  #Fact    : 0
% 12.46/4.68  #Define  : 0
% 12.46/4.68  #Split   : 80
% 12.46/4.68  #Chain   : 0
% 12.46/4.68  #Close   : 0
% 12.46/4.68  
% 12.46/4.68  Ordering : KBO
% 12.46/4.68  
% 12.46/4.68  Simplification rules
% 12.46/4.68  ----------------------
% 12.46/4.68  #Subsume      : 1368
% 12.46/4.68  #Demod        : 10684
% 12.46/4.68  #Tautology    : 2753
% 12.46/4.68  #SimpNegUnit  : 105
% 12.46/4.68  #BackRed      : 944
% 12.46/4.68  
% 12.46/4.68  #Partial instantiations: 0
% 12.46/4.68  #Strategies tried      : 1
% 12.46/4.68  
% 12.46/4.68  Timing (in seconds)
% 12.46/4.68  ----------------------
% 12.46/4.68  Preprocessing        : 0.36
% 12.46/4.68  Parsing              : 0.19
% 12.46/4.68  CNF conversion       : 0.02
% 12.46/4.68  Main loop            : 3.42
% 12.46/4.68  Inferencing          : 1.15
% 12.46/4.68  Reduction            : 1.26
% 12.46/4.68  Demodulation         : 0.91
% 12.46/4.68  BG Simplification    : 0.12
% 12.46/4.68  Subsumption          : 0.60
% 12.46/4.68  Abstraction          : 0.17
% 12.46/4.68  MUC search           : 0.00
% 12.46/4.68  Cooper               : 0.00
% 12.46/4.68  Total                : 3.98
% 12.46/4.68  Index Insertion      : 0.00
% 12.46/4.68  Index Deletion       : 0.00
% 12.46/4.68  Index Matching       : 0.00
% 12.46/4.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
