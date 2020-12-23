%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:45 EST 2020

% Result     : Theorem 11.32s
% Output     : CNFRefutation 11.85s
% Verified   : 
% Statistics : Number of formulae       :  561 (13691 expanded)
%              Number of leaves         :   33 (3950 expanded)
%              Depth                    :   22
%              Number of atoms          :  990 (35552 expanded)
%              Number of equality atoms :  346 (14308 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_103,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_103,plain,(
    ! [A_32] :
      ( v1_funct_1(k2_funct_1(A_32))
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_58,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_102,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_106,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_102])).

tff(c_109,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_106])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_131,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_138,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_131])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_138])).

tff(c_148,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_150,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_166,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_179,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_166])).

tff(c_62,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_430,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_relset_1(A_85,B_86,C_87) = k2_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_440,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_430])).

tff(c_450,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_440])).

tff(c_24,plain,(
    ! [A_8] :
      ( k1_relat_1(k2_funct_1(A_8)) = k2_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_7] :
      ( v1_relat_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_149,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_282,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_297,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_282])).

tff(c_7901,plain,(
    ! [B_477,A_478,C_479] :
      ( k1_xboole_0 = B_477
      | k1_relset_1(A_478,B_477,C_479) = A_478
      | ~ v1_funct_2(C_479,A_478,B_477)
      | ~ m1_subset_1(C_479,k1_zfmisc_1(k2_zfmisc_1(A_478,B_477))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_7929,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_7901])).

tff(c_7947,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_297,c_7929])).

tff(c_7949,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7947])).

tff(c_270,plain,(
    ! [A_62] :
      ( k2_relat_1(k2_funct_1(A_62)) = k1_relat_1(A_62)
      | ~ v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    ! [A_24] :
      ( v1_funct_2(A_24,k1_relat_1(A_24),k2_relat_1(A_24))
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_11312,plain,(
    ! [A_662] :
      ( v1_funct_2(k2_funct_1(A_662),k1_relat_1(k2_funct_1(A_662)),k1_relat_1(A_662))
      | ~ v1_funct_1(k2_funct_1(A_662))
      | ~ v1_relat_1(k2_funct_1(A_662))
      | ~ v2_funct_1(A_662)
      | ~ v1_funct_1(A_662)
      | ~ v1_relat_1(A_662) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_48])).

tff(c_11315,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7949,c_11312])).

tff(c_11326,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_149,c_11315])).

tff(c_11329,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_11326])).

tff(c_11332,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_11329])).

tff(c_11336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_11332])).

tff(c_11338,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_11326])).

tff(c_22,plain,(
    ! [A_8] :
      ( k2_relat_1(k2_funct_1(A_8)) = k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_317,plain,(
    ! [A_69] :
      ( m1_subset_1(A_69,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_69),k2_relat_1(A_69))))
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_12244,plain,(
    ! [A_692] :
      ( m1_subset_1(k2_funct_1(A_692),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_692)),k1_relat_1(A_692))))
      | ~ v1_funct_1(k2_funct_1(A_692))
      | ~ v1_relat_1(k2_funct_1(A_692))
      | ~ v2_funct_1(A_692)
      | ~ v1_funct_1(A_692)
      | ~ v1_relat_1(A_692) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_317])).

tff(c_12267,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7949,c_12244])).

tff(c_12285,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_11338,c_149,c_12267])).

tff(c_12310,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_12285])).

tff(c_12323,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_450,c_12310])).

tff(c_12325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_12323])).

tff(c_12326,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7947])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12361,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12326,c_12326,c_10])).

tff(c_12401,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12361,c_64])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12360,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12326,c_12326,c_12])).

tff(c_153,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_153])).

tff(c_12400,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12361,c_161])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7486,plain,(
    ! [B_455,C_456] :
      ( k2_relset_1(k1_xboole_0,B_455,C_456) = k2_relat_1(C_456)
      | ~ m1_subset_1(C_456,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_430])).

tff(c_7493,plain,(
    ! [B_455,A_5] :
      ( k2_relset_1(k1_xboole_0,B_455,A_5) = k2_relat_1(A_5)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_7486])).

tff(c_12921,plain,(
    ! [B_731,A_732] :
      ( k2_relset_1('#skF_2',B_731,A_732) = k2_relat_1(A_732)
      | ~ r1_tarski(A_732,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12326,c_12326,c_7493])).

tff(c_12926,plain,(
    ! [B_731] : k2_relset_1('#skF_2',B_731,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12400,c_12921])).

tff(c_12936,plain,(
    ! [B_733] : k2_relset_1('#skF_2',B_733,'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_12926])).

tff(c_28,plain,(
    ! [A_12,B_13,C_14] :
      ( m1_subset_1(k2_relset_1(A_12,B_13,C_14),k1_zfmisc_1(B_13))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12948,plain,(
    ! [B_733] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(B_733))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_733))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12936,c_28])).

tff(c_12963,plain,(
    ! [B_734] : m1_subset_1('#skF_2',k1_zfmisc_1(B_734)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12401,c_12360,c_12948])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_13010,plain,(
    ! [B_734] : r1_tarski('#skF_2',B_734) ),
    inference(resolution,[status(thm)],[c_12963,c_14])).

tff(c_214,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(B_55,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_219,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_214])).

tff(c_235,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_12399,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12361,c_235])).

tff(c_13013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13010,c_12399])).

tff(c_13014,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_13018,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13014,c_64])).

tff(c_13263,plain,(
    ! [A_763,B_764,C_765] :
      ( k2_relset_1(A_763,B_764,C_765) = k2_relat_1(C_765)
      | ~ m1_subset_1(C_765,k1_zfmisc_1(k2_zfmisc_1(A_763,B_764))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_13318,plain,(
    ! [C_775] :
      ( k2_relset_1('#skF_1','#skF_2',C_775) = k2_relat_1(C_775)
      | ~ m1_subset_1(C_775,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13014,c_13263])).

tff(c_13321,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_13018,c_13318])).

tff(c_13327,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_13321])).

tff(c_13080,plain,(
    ! [A_739] :
      ( k1_relat_1(k2_funct_1(A_739)) = k2_relat_1(A_739)
      | ~ v2_funct_1(A_739)
      | ~ v1_funct_1(A_739)
      | ~ v1_relat_1(A_739) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_17863,plain,(
    ! [A_994] :
      ( v1_funct_2(k2_funct_1(A_994),k2_relat_1(A_994),k2_relat_1(k2_funct_1(A_994)))
      | ~ v1_funct_1(k2_funct_1(A_994))
      | ~ v1_relat_1(k2_funct_1(A_994))
      | ~ v2_funct_1(A_994)
      | ~ v1_funct_1(A_994)
      | ~ v1_relat_1(A_994) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13080,c_48])).

tff(c_17875,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13327,c_17863])).

tff(c_17887,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_149,c_17875])).

tff(c_17888,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_17887])).

tff(c_17891,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_17888])).

tff(c_17895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_17891])).

tff(c_17897,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_17887])).

tff(c_13104,plain,(
    ! [A_741,B_742,C_743] :
      ( k1_relset_1(A_741,B_742,C_743) = k1_relat_1(C_743)
      | ~ m1_subset_1(C_743,k1_zfmisc_1(k2_zfmisc_1(A_741,B_742))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_13188,plain,(
    ! [C_755] :
      ( k1_relset_1('#skF_1','#skF_2',C_755) = k1_relat_1(C_755)
      | ~ m1_subset_1(C_755,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13014,c_13104])).

tff(c_13196,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_13018,c_13188])).

tff(c_13991,plain,(
    ! [B_803,C_804,A_805] :
      ( k1_xboole_0 = B_803
      | v1_funct_2(C_804,A_805,B_803)
      | k1_relset_1(A_805,B_803,C_804) != A_805
      | ~ m1_subset_1(C_804,k1_zfmisc_1(k2_zfmisc_1(A_805,B_803))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14011,plain,(
    ! [C_804] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_804,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_804) != '#skF_1'
      | ~ m1_subset_1(C_804,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13014,c_13991])).

tff(c_14035,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_14011])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13023,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_13014,c_8])).

tff(c_13047,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_13023])).

tff(c_14062,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14035,c_13047])).

tff(c_14139,plain,(
    ! [A_810] : k2_zfmisc_1(A_810,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14035,c_14035,c_10])).

tff(c_14165,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_14139,c_13014])).

tff(c_14184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14062,c_14165])).

tff(c_14186,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14011])).

tff(c_14297,plain,(
    ! [B_821,A_822,C_823] :
      ( k1_xboole_0 = B_821
      | k1_relset_1(A_822,B_821,C_823) = A_822
      | ~ v1_funct_2(C_823,A_822,B_821)
      | ~ m1_subset_1(C_823,k1_zfmisc_1(k2_zfmisc_1(A_822,B_821))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14317,plain,(
    ! [C_823] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_823) = '#skF_1'
      | ~ v1_funct_2(C_823,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_823,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13014,c_14297])).

tff(c_14358,plain,(
    ! [C_826] :
      ( k1_relset_1('#skF_1','#skF_2',C_826) = '#skF_1'
      | ~ v1_funct_2(C_826,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_826,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14186,c_14317])).

tff(c_14369,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_13018,c_14358])).

tff(c_14379,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_13196,c_14369])).

tff(c_13163,plain,(
    ! [A_752] :
      ( m1_subset_1(A_752,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_752),k2_relat_1(A_752))))
      | ~ v1_funct_1(A_752)
      | ~ v1_relat_1(A_752) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_18896,plain,(
    ! [A_1038] :
      ( m1_subset_1(k2_funct_1(A_1038),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1038)),k1_relat_1(A_1038))))
      | ~ v1_funct_1(k2_funct_1(A_1038))
      | ~ v1_relat_1(k2_funct_1(A_1038))
      | ~ v2_funct_1(A_1038)
      | ~ v1_funct_1(A_1038)
      | ~ v1_relat_1(A_1038) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_13163])).

tff(c_18919,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14379,c_18896])).

tff(c_18934,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_17897,c_149,c_18919])).

tff(c_18957,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_18934])).

tff(c_18970,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_13327,c_18957])).

tff(c_18972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_18970])).

tff(c_18974,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_13023])).

tff(c_18979,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18974,c_18974,c_12])).

tff(c_18973,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_13023])).

tff(c_18986,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18974,c_18974,c_18973])).

tff(c_18987,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18986])).

tff(c_19001,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18987,c_150])).

tff(c_19053,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18979,c_19001])).

tff(c_18980,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18974,c_18974,c_10])).

tff(c_19198,plain,(
    ! [A_1067,B_1068,C_1069] :
      ( k2_relset_1(A_1067,B_1068,C_1069) = k2_relat_1(C_1069)
      | ~ m1_subset_1(C_1069,k1_zfmisc_1(k2_zfmisc_1(A_1067,B_1068))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_19254,plain,(
    ! [A_1076,C_1077] :
      ( k2_relset_1(A_1076,'#skF_3',C_1077) = k2_relat_1(C_1077)
      | ~ m1_subset_1(C_1077,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18980,c_19198])).

tff(c_19262,plain,(
    ! [A_1078] : k2_relset_1(A_1078,'#skF_3','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_13018,c_19254])).

tff(c_19002,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18987,c_18987,c_60])).

tff(c_19269,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_19262,c_19002])).

tff(c_19915,plain,(
    ! [B_1127,A_1128] :
      ( m1_subset_1(B_1127,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1127),A_1128)))
      | ~ r1_tarski(k2_relat_1(B_1127),A_1128)
      | ~ v1_funct_1(B_1127)
      | ~ v1_relat_1(B_1127) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_19381,plain,(
    ! [A_1089,B_1090,C_1091] :
      ( m1_subset_1(k2_relset_1(A_1089,B_1090,C_1091),k1_zfmisc_1(B_1090))
      | ~ m1_subset_1(C_1091,k1_zfmisc_1(k2_zfmisc_1(A_1089,B_1090))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_19432,plain,(
    ! [A_1089,B_1090,C_1091] :
      ( r1_tarski(k2_relset_1(A_1089,B_1090,C_1091),B_1090)
      | ~ m1_subset_1(C_1091,k1_zfmisc_1(k2_zfmisc_1(A_1089,B_1090))) ) ),
    inference(resolution,[status(thm)],[c_19381,c_14])).

tff(c_20686,plain,(
    ! [B_1189,A_1190] :
      ( r1_tarski(k2_relset_1(k1_relat_1(B_1189),A_1190,B_1189),A_1190)
      | ~ r1_tarski(k2_relat_1(B_1189),A_1190)
      | ~ v1_funct_1(B_1189)
      | ~ v1_relat_1(B_1189) ) ),
    inference(resolution,[status(thm)],[c_19915,c_19432])).

tff(c_178,plain,(
    ! [A_5,A_46,B_47] :
      ( v1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_46,B_47)) ) ),
    inference(resolution,[status(thm)],[c_16,c_166])).

tff(c_13027,plain,(
    ! [A_5] :
      ( v1_relat_1(A_5)
      | ~ r1_tarski(A_5,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13014,c_178])).

tff(c_20759,plain,(
    ! [B_1191] :
      ( v1_relat_1(k2_relset_1(k1_relat_1(B_1191),'#skF_3',B_1191))
      | ~ r1_tarski(k2_relat_1(B_1191),'#skF_3')
      | ~ v1_funct_1(B_1191)
      | ~ v1_relat_1(B_1191) ) ),
    inference(resolution,[status(thm)],[c_20686,c_13027])).

tff(c_21152,plain,(
    ! [A_1209] :
      ( v1_relat_1(k2_relset_1(k2_relat_1(A_1209),'#skF_3',k2_funct_1(A_1209)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_1209)),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(A_1209))
      | ~ v1_relat_1(k2_funct_1(A_1209))
      | ~ v2_funct_1(A_1209)
      | ~ v1_funct_1(A_1209)
      | ~ v1_relat_1(A_1209) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_20759])).

tff(c_21155,plain,
    ( v1_relat_1(k2_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_3')))
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_19269,c_21152])).

tff(c_21160,plain,
    ( v1_relat_1(k2_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_3')))
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_149,c_21155])).

tff(c_21271,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_21160])).

tff(c_21274,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_21271])).

tff(c_21278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_21274])).

tff(c_21280,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_21160])).

tff(c_19218,plain,(
    ! [A_1072] :
      ( m1_subset_1(A_1072,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1072),k2_relat_1(A_1072))))
      | ~ v1_funct_1(A_1072)
      | ~ v1_relat_1(A_1072) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_21998,plain,(
    ! [A_1242] :
      ( m1_subset_1(k2_funct_1(A_1242),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1242),k2_relat_1(k2_funct_1(A_1242)))))
      | ~ v1_funct_1(k2_funct_1(A_1242))
      | ~ v1_relat_1(k2_funct_1(A_1242))
      | ~ v2_funct_1(A_1242)
      | ~ v1_funct_1(A_1242)
      | ~ v1_relat_1(A_1242) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_19218])).

tff(c_22024,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_19269,c_21998])).

tff(c_22040,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_21280,c_149,c_18979,c_22024])).

tff(c_22042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19053,c_22040])).

tff(c_22043,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18986])).

tff(c_22071,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22043,c_22043,c_18980])).

tff(c_22051,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22043,c_150])).

tff(c_22150,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22071,c_22051])).

tff(c_22050,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22043,c_179])).

tff(c_22056,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22043,c_68])).

tff(c_22055,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22043,c_62])).

tff(c_22052,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22043,c_149])).

tff(c_22047,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22043,c_22043,c_13018])).

tff(c_22089,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22043,c_22043,c_18979])).

tff(c_22179,plain,(
    ! [A_1252,B_1253,C_1254] :
      ( k2_relset_1(A_1252,B_1253,C_1254) = k2_relat_1(C_1254)
      | ~ m1_subset_1(C_1254,k1_zfmisc_1(k2_zfmisc_1(A_1252,B_1253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22191,plain,(
    ! [B_1255,C_1256] :
      ( k2_relset_1('#skF_1',B_1255,C_1256) = k2_relat_1(C_1256)
      | ~ m1_subset_1(C_1256,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22089,c_22179])).

tff(c_22199,plain,(
    ! [B_1257] : k2_relset_1('#skF_1',B_1257,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22047,c_22191])).

tff(c_22053,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22043,c_60])).

tff(c_22203,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_22199,c_22053])).

tff(c_22137,plain,(
    ! [A_1248] :
      ( k1_relat_1(k2_funct_1(A_1248)) = k2_relat_1(A_1248)
      | ~ v2_funct_1(A_1248)
      | ~ v1_funct_1(A_1248)
      | ~ v1_relat_1(A_1248) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24822,plain,(
    ! [A_1428] :
      ( v1_funct_2(k2_funct_1(A_1428),k2_relat_1(A_1428),k2_relat_1(k2_funct_1(A_1428)))
      | ~ v1_funct_1(k2_funct_1(A_1428))
      | ~ v1_relat_1(k2_funct_1(A_1428))
      | ~ v2_funct_1(A_1428)
      | ~ v1_funct_1(A_1428)
      | ~ v1_relat_1(A_1428) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22137,c_48])).

tff(c_24831,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),'#skF_2',k2_relat_1(k2_funct_1('#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22203,c_24822])).

tff(c_24843,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),'#skF_2',k2_relat_1(k2_funct_1('#skF_1')))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22050,c_22056,c_22055,c_22052,c_24831])).

tff(c_24844,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_24843])).

tff(c_24847,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_24844])).

tff(c_24851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22050,c_22056,c_24847])).

tff(c_24853,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_24843])).

tff(c_22044,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18986])).

tff(c_22061,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22043,c_22044])).

tff(c_22210,plain,(
    ! [A_1258,B_1259,C_1260] :
      ( k1_relset_1(A_1258,B_1259,C_1260) = k1_relat_1(C_1260)
      | ~ m1_subset_1(C_1260,k1_zfmisc_1(k2_zfmisc_1(A_1258,B_1259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22277,plain,(
    ! [B_1269,C_1270] :
      ( k1_relset_1('#skF_1',B_1269,C_1270) = k1_relat_1(C_1270)
      | ~ m1_subset_1(C_1270,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22089,c_22210])).

tff(c_22283,plain,(
    ! [B_1269] : k1_relset_1('#skF_1',B_1269,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22047,c_22277])).

tff(c_22054,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22043,c_66])).

tff(c_22045,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22043,c_18974])).

tff(c_42,plain,(
    ! [B_22,C_23] :
      ( k1_relset_1(k1_xboole_0,B_22,C_23) = k1_xboole_0
      | ~ v1_funct_2(C_23,k1_xboole_0,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_70,plain,(
    ! [B_22,C_23] :
      ( k1_relset_1(k1_xboole_0,B_22,C_23) = k1_xboole_0
      | ~ v1_funct_2(C_23,k1_xboole_0,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_42])).

tff(c_22534,plain,(
    ! [B_1295,C_1296] :
      ( k1_relset_1('#skF_1',B_1295,C_1296) = '#skF_1'
      | ~ v1_funct_2(C_1296,'#skF_1',B_1295)
      | ~ m1_subset_1(C_1296,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22045,c_22045,c_22045,c_22045,c_70])).

tff(c_22536,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22054,c_22534])).

tff(c_22542,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22047,c_22283,c_22536])).

tff(c_22285,plain,(
    ! [A_1271] :
      ( m1_subset_1(A_1271,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1271),k2_relat_1(A_1271))))
      | ~ v1_funct_1(A_1271)
      | ~ v1_relat_1(A_1271) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22300,plain,
    ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_2')))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22203,c_22285])).

tff(c_22312,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22050,c_22056,c_22300])).

tff(c_22337,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_22312,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22347,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_2') = '#skF_1'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_22337,c_2])).

tff(c_22448,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22347])).

tff(c_22547,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22542,c_22448])).

tff(c_22557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22089,c_22547])).

tff(c_22558,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_22347])).

tff(c_18975,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_3'
      | A_3 = '#skF_3'
      | k2_zfmisc_1(A_3,B_4) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18974,c_18974,c_18974,c_8])).

tff(c_22155,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_1'
      | A_3 = '#skF_1'
      | k2_zfmisc_1(A_3,B_4) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22043,c_22043,c_22043,c_18975])).

tff(c_22582,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_22558,c_22155])).

tff(c_22594,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_22061,c_22582])).

tff(c_25084,plain,(
    ! [A_1440] :
      ( m1_subset_1(k2_funct_1(A_1440),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1440)),k1_relat_1(A_1440))))
      | ~ v1_funct_1(k2_funct_1(A_1440))
      | ~ v1_relat_1(k2_funct_1(A_1440))
      | ~ v2_funct_1(A_1440)
      | ~ v1_funct_1(A_1440)
      | ~ v1_relat_1(A_1440) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_22285])).

tff(c_25107,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22594,c_25084])).

tff(c_25122,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22050,c_22056,c_22055,c_24853,c_22052,c_22071,c_25107])).

tff(c_25124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22150,c_25122])).

tff(c_25125,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_25142,plain,(
    ! [C_1445,A_1446,B_1447] :
      ( v1_relat_1(C_1445)
      | ~ m1_subset_1(C_1445,k1_zfmisc_1(k2_zfmisc_1(A_1446,B_1447))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_25159,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_25142])).

tff(c_26912,plain,(
    ! [A_1544,B_1545,C_1546] :
      ( k2_relset_1(A_1544,B_1545,C_1546) = k2_relat_1(C_1546)
      | ~ m1_subset_1(C_1546,k1_zfmisc_1(k2_zfmisc_1(A_1544,B_1545))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26922,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_26912])).

tff(c_26931,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_26922])).

tff(c_25126,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_25157,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_25126,c_25142])).

tff(c_27131,plain,(
    ! [A_1566,B_1567,C_1568] :
      ( k1_relset_1(A_1566,B_1567,C_1568) = k1_relat_1(C_1568)
      | ~ m1_subset_1(C_1568,k1_zfmisc_1(k2_zfmisc_1(A_1566,B_1567))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_27157,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_27131])).

tff(c_28150,plain,(
    ! [B_1623,A_1624,C_1625] :
      ( k1_xboole_0 = B_1623
      | k1_relset_1(A_1624,B_1623,C_1625) = A_1624
      | ~ v1_funct_2(C_1625,A_1624,B_1623)
      | ~ m1_subset_1(C_1625,k1_zfmisc_1(k2_zfmisc_1(A_1624,B_1623))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28177,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_28150])).

tff(c_28196,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_27157,c_28177])).

tff(c_28198,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_28196])).

tff(c_25432,plain,(
    ! [A_1485,B_1486,C_1487] :
      ( k2_relset_1(A_1485,B_1486,C_1487) = k2_relat_1(C_1487)
      | ~ m1_subset_1(C_1487,k1_zfmisc_1(k2_zfmisc_1(A_1485,B_1486))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_25445,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_25432])).

tff(c_25456,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_25445])).

tff(c_25300,plain,(
    ! [A_1465,B_1466,C_1467] :
      ( k1_relset_1(A_1465,B_1466,C_1467) = k1_relat_1(C_1467)
      | ~ m1_subset_1(C_1467,k1_zfmisc_1(k2_zfmisc_1(A_1465,B_1466))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_25321,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_25126,c_25300])).

tff(c_25932,plain,(
    ! [B_1514,C_1515,A_1516] :
      ( k1_xboole_0 = B_1514
      | v1_funct_2(C_1515,A_1516,B_1514)
      | k1_relset_1(A_1516,B_1514,C_1515) != A_1516
      | ~ m1_subset_1(C_1515,k1_zfmisc_1(k2_zfmisc_1(A_1516,B_1514))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_25952,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_25126,c_25932])).

tff(c_25975,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25321,c_25952])).

tff(c_25976,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_25125,c_25975])).

tff(c_25981,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_25976])).

tff(c_25984,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_25981])).

tff(c_25987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25159,c_68,c_62,c_25456,c_25984])).

tff(c_25988,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_25976])).

tff(c_26021,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25988,c_25988,c_12])).

tff(c_26144,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26021,c_64])).

tff(c_25323,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_25300])).

tff(c_44,plain,(
    ! [B_22,A_21,C_23] :
      ( k1_xboole_0 = B_22
      | k1_relset_1(A_21,B_22,C_23) = A_21
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26107,plain,(
    ! [B_1518,A_1519,C_1520] :
      ( B_1518 = '#skF_1'
      | k1_relset_1(A_1519,B_1518,C_1520) = A_1519
      | ~ v1_funct_2(C_1520,A_1519,B_1518)
      | ~ m1_subset_1(C_1520,k1_zfmisc_1(k2_zfmisc_1(A_1519,B_1518))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25988,c_44])).

tff(c_26130,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_26107])).

tff(c_26141,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_25323,c_26130])).

tff(c_26249,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_26141])).

tff(c_25453,plain,(
    k2_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_25126,c_25432])).

tff(c_25583,plain,(
    ! [A_1500,B_1501,C_1502] :
      ( m1_subset_1(k2_relset_1(A_1500,B_1501,C_1502),k1_zfmisc_1(B_1501))
      | ~ m1_subset_1(C_1502,k1_zfmisc_1(k2_zfmisc_1(A_1500,B_1501))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_25626,plain,
    ( m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_25453,c_25583])).

tff(c_25654,plain,(
    m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25126,c_25626])).

tff(c_25802,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_25654,c_14])).

tff(c_25809,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_25802])).

tff(c_25812,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25159,c_68,c_62,c_25809])).

tff(c_25815,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_25812,c_2])).

tff(c_25834,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_25815])).

tff(c_26251,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26249,c_25834])).

tff(c_26264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_26251])).

tff(c_26265,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26141])).

tff(c_26277,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26265,c_25456])).

tff(c_25448,plain,(
    ! [B_4,C_1487] :
      ( k2_relset_1(k1_xboole_0,B_4,C_1487) = k2_relat_1(C_1487)
      | ~ m1_subset_1(C_1487,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_25432])).

tff(c_26555,plain,(
    ! [B_1533,C_1534] :
      ( k2_relset_1('#skF_1',B_1533,C_1534) = k2_relat_1(C_1534)
      | ~ m1_subset_1(C_1534,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25988,c_25988,c_25448])).

tff(c_26564,plain,(
    ! [B_1533] : k2_relset_1('#skF_1',B_1533,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26144,c_26555])).

tff(c_26590,plain,(
    ! [B_1535] : k2_relset_1('#skF_1',B_1535,'#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26277,c_26564])).

tff(c_26595,plain,(
    ! [B_1535] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(B_1535))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_1535))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26590,c_28])).

tff(c_26603,plain,(
    ! [B_1536] : m1_subset_1('#skF_1',k1_zfmisc_1(B_1536)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26144,c_26021,c_26595])).

tff(c_26639,plain,(
    ! [B_1536] : r1_tarski('#skF_1',B_1536) ),
    inference(resolution,[status(thm)],[c_26603,c_14])).

tff(c_26022,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25988,c_25988,c_10])).

tff(c_25129,plain,(
    ! [A_1443,B_1444] :
      ( r1_tarski(A_1443,B_1444)
      | ~ m1_subset_1(A_1443,k1_zfmisc_1(B_1444)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25139,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_25126,c_25129])).

tff(c_25160,plain,(
    ! [B_1448,A_1449] :
      ( B_1448 = A_1449
      | ~ r1_tarski(B_1448,A_1449)
      | ~ r1_tarski(A_1449,B_1448) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_25167,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_25139,c_25160])).

tff(c_25235,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_25167])).

tff(c_26067,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26022,c_25235])).

tff(c_26648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26639,c_26067])).

tff(c_26649,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_25815])).

tff(c_25810,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_25802,c_2])).

tff(c_26651,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_25810])).

tff(c_26698,plain,
    ( ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_26651])).

tff(c_26701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25159,c_68,c_62,c_6,c_26649,c_26698])).

tff(c_26702,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_25810])).

tff(c_26787,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26702,c_48])).

tff(c_26800,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25157,c_149,c_26787])).

tff(c_26828,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_26800])).

tff(c_26830,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25159,c_68,c_62,c_25456,c_26828])).

tff(c_26832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25125,c_26830])).

tff(c_26833,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_25167])).

tff(c_26846,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26833,c_25126])).

tff(c_26941,plain,(
    ! [C_1547] :
      ( k2_relset_1('#skF_2','#skF_1',C_1547) = k2_relat_1(C_1547)
      | ~ m1_subset_1(C_1547,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26833,c_26912])).

tff(c_26949,plain,(
    k2_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26846,c_26941])).

tff(c_27335,plain,(
    ! [A_1590,B_1591,C_1592] :
      ( m1_subset_1(k2_relset_1(A_1590,B_1591,C_1592),k1_zfmisc_1(B_1591))
      | ~ m1_subset_1(C_1592,k1_zfmisc_1(k2_zfmisc_1(A_1590,B_1591))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_27396,plain,
    ( m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26949,c_27335])).

tff(c_27424,plain,(
    m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26846,c_26833,c_27396])).

tff(c_27458,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_27424])).

tff(c_27461,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25159,c_68,c_62,c_27458])).

tff(c_27604,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_27461,c_14])).

tff(c_27625,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_27604,c_2])).

tff(c_27673,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_27625])).

tff(c_28199,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28198,c_27673])).

tff(c_28211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_28199])).

tff(c_28212,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28196])).

tff(c_26851,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26833,c_8])).

tff(c_26876,plain,(
    k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_26851])).

tff(c_28241,plain,(
    k2_funct_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28212,c_26876])).

tff(c_28248,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28212,c_28212,c_12])).

tff(c_28308,plain,(
    k2_funct_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28248,c_26833])).

tff(c_28310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28241,c_28308])).

tff(c_28311,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_27625])).

tff(c_27459,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_27424,c_14])).

tff(c_27631,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_27459,c_2])).

tff(c_29103,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_27631])).

tff(c_29106,plain,
    ( ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_29103])).

tff(c_29109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25159,c_68,c_62,c_6,c_28311,c_29106])).

tff(c_29110,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_27631])).

tff(c_29156,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29110,c_48])).

tff(c_29173,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25157,c_149,c_29156])).

tff(c_29194,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_29173])).

tff(c_29196,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25159,c_68,c_62,c_26931,c_29194])).

tff(c_29198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25125,c_29196])).

tff(c_29199,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26851])).

tff(c_29241,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_29199])).

tff(c_34,plain,(
    ! [A_21] :
      ( v1_funct_2(k1_xboole_0,A_21,k1_xboole_0)
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_21,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_71,plain,(
    ! [A_21] :
      ( v1_funct_2(k1_xboole_0,A_21,k1_xboole_0)
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_34])).

tff(c_25225,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_25228,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_25225])).

tff(c_25232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_25228])).

tff(c_25233,plain,(
    ! [A_21] :
      ( v1_funct_2(k1_xboole_0,A_21,k1_xboole_0)
      | k1_xboole_0 = A_21 ) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_29431,plain,(
    ! [A_1671] :
      ( v1_funct_2('#skF_1',A_1671,'#skF_1')
      | A_1671 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29241,c_29241,c_29241,c_25233])).

tff(c_29200,plain,(
    k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26851])).

tff(c_29205,plain,(
    ~ v1_funct_2(k1_xboole_0,'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29200,c_25125])).

tff(c_29242,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29241,c_29205])).

tff(c_29435,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_29431,c_29242])).

tff(c_29452,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29435,c_29242])).

tff(c_29244,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29241,c_29200])).

tff(c_29288,plain,(
    ! [A_1665] :
      ( k1_relat_1(k2_funct_1(A_1665)) = k2_relat_1(A_1665)
      | ~ v2_funct_1(A_1665)
      | ~ v1_funct_1(A_1665)
      | ~ v1_relat_1(A_1665) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_29300,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29244,c_29288])).

tff(c_29304,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25159,c_68,c_62,c_29300])).

tff(c_29251,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29241,c_29241,c_12])).

tff(c_29322,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29251,c_64])).

tff(c_29436,plain,(
    ! [A_1672,B_1673,C_1674] :
      ( k2_relset_1(A_1672,B_1673,C_1674) = k2_relat_1(C_1674)
      | ~ m1_subset_1(C_1674,k1_zfmisc_1(k2_zfmisc_1(A_1672,B_1673))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_29578,plain,(
    ! [B_1682,C_1683] :
      ( k2_relset_1('#skF_1',B_1682,C_1683) = k2_relat_1(C_1683)
      | ~ m1_subset_1(C_1683,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29251,c_29436])).

tff(c_29582,plain,(
    ! [B_1682] : k2_relset_1('#skF_1',B_1682,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_29322,c_29578])).

tff(c_29598,plain,(
    ! [B_1685] : k2_relset_1('#skF_1',B_1685,'#skF_3') = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29304,c_29582])).

tff(c_29453,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29435,c_29435,c_60])).

tff(c_29602,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_29598,c_29453])).

tff(c_29395,plain,
    ( v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29304,c_48])).

tff(c_29401,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25159,c_68,c_29395])).

tff(c_29618,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29602,c_29401])).

tff(c_36,plain,(
    ! [C_23,A_21] :
      ( k1_xboole_0 = C_23
      | ~ v1_funct_2(C_23,A_21,k1_xboole_0)
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_72,plain,(
    ! [C_23,A_21] :
      ( k1_xboole_0 = C_23
      | ~ v1_funct_2(C_23,A_21,k1_xboole_0)
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_36])).

tff(c_29560,plain,(
    ! [C_23,A_21] :
      ( C_23 = '#skF_1'
      | ~ v1_funct_2(C_23,A_21,'#skF_1')
      | A_21 = '#skF_1'
      | ~ m1_subset_1(C_23,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29241,c_29241,c_29241,c_29241,c_72])).

tff(c_29676,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_29618,c_29560])).

tff(c_29679,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29322,c_29676])).

tff(c_29690,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_29679])).

tff(c_25173,plain,(
    ! [C_1450] :
      ( v1_relat_1(C_1450)
      | ~ m1_subset_1(C_1450,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_25142])).

tff(c_25179,plain,(
    ! [A_1451] :
      ( v1_relat_1(A_1451)
      | ~ r1_tarski(A_1451,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_25173])).

tff(c_25184,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_25179])).

tff(c_29248,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29241,c_25184])).

tff(c_29206,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29200,c_149])).

tff(c_29243,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29241,c_29206])).

tff(c_29223,plain,(
    ! [A_1664] :
      ( k2_relat_1(k2_funct_1(A_1664)) = k1_relat_1(A_1664)
      | ~ v2_funct_1(A_1664)
      | ~ v1_funct_1(A_1664)
      | ~ v1_relat_1(A_1664) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_29235,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29200,c_29223])).

tff(c_29239,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25159,c_68,c_62,c_29235])).

tff(c_29358,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29241,c_29239])).

tff(c_29362,plain,
    ( v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_29358,c_48])).

tff(c_29366,plain,(
    v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29248,c_29243,c_29362])).

tff(c_29619,plain,(
    v1_funct_2('#skF_1','#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29602,c_29366])).

tff(c_29692,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29690,c_29619])).

tff(c_29697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29452,c_29692])).

tff(c_29698,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_29679])).

tff(c_29701,plain,(
    v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29698,c_29698,c_29618])).

tff(c_29715,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29602,c_29701])).

tff(c_29717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29452,c_29715])).

tff(c_29718,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_29199])).

tff(c_29719,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_29199])).

tff(c_29734,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29718,c_29719])).

tff(c_29729,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29718,c_29718,c_10])).

tff(c_29791,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29729,c_64])).

tff(c_30039,plain,(
    ! [C_1706,A_1707] :
      ( C_1706 = '#skF_2'
      | ~ v1_funct_2(C_1706,A_1707,'#skF_2')
      | A_1707 = '#skF_2'
      | ~ m1_subset_1(C_1706,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29718,c_29718,c_29718,c_29718,c_72])).

tff(c_30043,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_30039])).

tff(c_30050,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29791,c_30043])).

tff(c_30051,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_29734,c_30050])).

tff(c_25141,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_25129])).

tff(c_25168,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_25141,c_25160])).

tff(c_25185,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_25168])).

tff(c_29789,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29729,c_25185])).

tff(c_30071,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30051,c_29789])).

tff(c_30085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_30071])).

tff(c_30086,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_25168])).

tff(c_30089,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30086,c_64])).

tff(c_30281,plain,(
    ! [A_1732,B_1733,C_1734] :
      ( k2_relset_1(A_1732,B_1733,C_1734) = k2_relat_1(C_1734)
      | ~ m1_subset_1(C_1734,k1_zfmisc_1(k2_zfmisc_1(A_1732,B_1733))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30407,plain,(
    ! [C_1752] :
      ( k2_relset_1('#skF_1','#skF_2',C_1752) = k2_relat_1(C_1752)
      | ~ m1_subset_1(C_1752,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30086,c_30281])).

tff(c_30410,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30089,c_30407])).

tff(c_30416,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_30410])).

tff(c_30225,plain,(
    ! [A_1722,B_1723,C_1724] :
      ( k1_relset_1(A_1722,B_1723,C_1724) = k1_relat_1(C_1724)
      | ~ m1_subset_1(C_1724,k1_zfmisc_1(k2_zfmisc_1(A_1722,B_1723))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30246,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_25126,c_30225])).

tff(c_31035,plain,(
    ! [B_1776,C_1777,A_1778] :
      ( k1_xboole_0 = B_1776
      | v1_funct_2(C_1777,A_1778,B_1776)
      | k1_relset_1(A_1778,B_1776,C_1777) != A_1778
      | ~ m1_subset_1(C_1777,k1_zfmisc_1(k2_zfmisc_1(A_1778,B_1776))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_31058,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_25126,c_31035])).

tff(c_31078,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30246,c_31058])).

tff(c_31079,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_25125,c_31078])).

tff(c_31082,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_31079])).

tff(c_31085,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_31082])).

tff(c_31088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25159,c_68,c_62,c_30416,c_31085])).

tff(c_31089,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_31079])).

tff(c_30138,plain,(
    ! [B_1713,A_1714] :
      ( k1_xboole_0 = B_1713
      | k1_xboole_0 = A_1714
      | k2_zfmisc_1(A_1714,B_1713) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30141,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_30086,c_30138])).

tff(c_30162,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30141])).

tff(c_31117,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31089,c_30162])).

tff(c_31122,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31089,c_31089,c_12])).

tff(c_31231,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31122,c_30086])).

tff(c_31233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31117,c_31231])).

tff(c_31235,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30141])).

tff(c_33650,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31235,c_31235,c_12])).

tff(c_31234,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30141])).

tff(c_33657,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31235,c_31235,c_31234])).

tff(c_33658,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_33657])).

tff(c_31241,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31235,c_31235,c_12])).

tff(c_31390,plain,(
    ! [A_1794,B_1795,C_1796] :
      ( k1_relset_1(A_1794,B_1795,C_1796) = k1_relat_1(C_1796)
      | ~ m1_subset_1(C_1796,k1_zfmisc_1(k2_zfmisc_1(A_1794,B_1795))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_31441,plain,(
    ! [B_1803,C_1804] :
      ( k1_relset_1('#skF_3',B_1803,C_1804) = k1_relat_1(C_1804)
      | ~ m1_subset_1(C_1804,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31241,c_31390])).

tff(c_31450,plain,(
    ! [B_1803] : k1_relset_1('#skF_3',B_1803,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30089,c_31441])).

tff(c_38,plain,(
    ! [C_23,B_22] :
      ( v1_funct_2(C_23,k1_xboole_0,B_22)
      | k1_relset_1(k1_xboole_0,B_22,C_23) != k1_xboole_0
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_69,plain,(
    ! [C_23,B_22] :
      ( v1_funct_2(C_23,k1_xboole_0,B_22)
      | k1_relset_1(k1_xboole_0,B_22,C_23) != k1_xboole_0
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_38])).

tff(c_31730,plain,(
    ! [C_1831,B_1832] :
      ( v1_funct_2(C_1831,'#skF_3',B_1832)
      | k1_relset_1('#skF_3',B_1832,C_1831) != '#skF_3'
      | ~ m1_subset_1(C_1831,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31235,c_31235,c_31235,c_31235,c_69])).

tff(c_31740,plain,(
    ! [B_1832] :
      ( v1_funct_2('#skF_3','#skF_3',B_1832)
      | k1_relset_1('#skF_3',B_1832,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_30089,c_31730])).

tff(c_31750,plain,(
    ! [B_1832] :
      ( v1_funct_2('#skF_3','#skF_3',B_1832)
      | k1_relat_1('#skF_3') != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31450,c_31740])).

tff(c_31805,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_31750])).

tff(c_31248,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31235,c_31235,c_31234])).

tff(c_31249,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_31248])).

tff(c_31252,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31249,c_25126])).

tff(c_31314,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31241,c_31252])).

tff(c_31452,plain,(
    ! [A_1805,B_1806,C_1807] :
      ( k2_relset_1(A_1805,B_1806,C_1807) = k2_relat_1(C_1807)
      | ~ m1_subset_1(C_1807,k1_zfmisc_1(k2_zfmisc_1(A_1805,B_1806))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_31576,plain,(
    ! [B_1821,C_1822] :
      ( k2_relset_1('#skF_3',B_1821,C_1822) = k2_relat_1(C_1822)
      | ~ m1_subset_1(C_1822,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31241,c_31452])).

tff(c_31703,plain,(
    ! [B_1830] : k2_relset_1('#skF_3',B_1830,k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_31314,c_31576])).

tff(c_31715,plain,(
    ! [B_1830] :
      ( m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1(B_1830))
      | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_1830))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31703,c_28])).

tff(c_31753,plain,(
    ! [B_1833] : m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1(B_1833)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31314,c_31241,c_31715])).

tff(c_31806,plain,(
    ! [B_1834] : r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),B_1834) ),
    inference(resolution,[status(thm)],[c_31753,c_14])).

tff(c_31829,plain,(
    ! [B_1834] :
      ( r1_tarski(k1_relat_1('#skF_3'),B_1834)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_31806])).

tff(c_31840,plain,(
    ! [B_1835] : r1_tarski(k1_relat_1('#skF_3'),B_1835) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25159,c_68,c_62,c_31829])).

tff(c_31600,plain,(
    ! [B_1825] : k2_relset_1('#skF_3',B_1825,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30089,c_31576])).

tff(c_31612,plain,(
    ! [B_1825] :
      ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1(B_1825))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_1825))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31600,c_28])).

tff(c_31622,plain,(
    ! [B_1826] : m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1(B_1826)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30089,c_31241,c_31612])).

tff(c_31665,plain,(
    ! [B_1827] : r1_tarski(k2_relat_1('#skF_3'),B_1827) ),
    inference(resolution,[status(thm)],[c_31622,c_14])).

tff(c_31688,plain,(
    ! [B_1827] :
      ( k2_relat_1('#skF_3') = B_1827
      | ~ r1_tarski(B_1827,k2_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_31665,c_2])).

tff(c_31861,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_31840,c_31688])).

tff(c_31242,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31235,c_31235,c_10])).

tff(c_32404,plain,(
    ! [A_1865,B_1866,A_1867] :
      ( k2_relset_1(A_1865,B_1866,A_1867) = k2_relat_1(A_1867)
      | ~ r1_tarski(A_1867,k2_zfmisc_1(A_1865,B_1866)) ) ),
    inference(resolution,[status(thm)],[c_16,c_31452])).

tff(c_32427,plain,(
    ! [A_1868,A_1869] :
      ( k2_relset_1(A_1868,'#skF_3',A_1869) = k2_relat_1(A_1869)
      | ~ r1_tarski(A_1869,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31242,c_32404])).

tff(c_32435,plain,(
    ! [A_1868] : k2_relset_1(A_1868,'#skF_3','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_32427])).

tff(c_32444,plain,(
    ! [A_1870] : k2_relset_1(A_1870,'#skF_3','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31861,c_32435])).

tff(c_31254,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31249,c_31249,c_60])).

tff(c_32457,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_32444,c_31254])).

tff(c_32472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31805,c_32457])).

tff(c_32474,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_31750])).

tff(c_31790,plain,(
    ! [B_1833] :
      ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1(B_1833))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_31753])).

tff(c_31804,plain,(
    ! [B_1833] : m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1(B_1833)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25159,c_68,c_62,c_31790])).

tff(c_32532,plain,(
    ! [B_1874] : m1_subset_1('#skF_3',k1_zfmisc_1(B_1874)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32474,c_31804])).

tff(c_32585,plain,(
    ! [B_1874] : r1_tarski('#skF_3',B_1874) ),
    inference(resolution,[status(thm)],[c_32532,c_14])).

tff(c_31236,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_25167])).

tff(c_31304,plain,(
    ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31241,c_31249,c_31236])).

tff(c_32602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32585,c_31304])).

tff(c_32603,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_31248])).

tff(c_32611,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32603,c_25159])).

tff(c_32619,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32603,c_68])).

tff(c_32618,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32603,c_62])).

tff(c_32608,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32603,c_32603,c_30089])).

tff(c_32630,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32603,c_32603,c_31241])).

tff(c_32755,plain,(
    ! [A_1887,B_1888,C_1889] :
      ( k1_relset_1(A_1887,B_1888,C_1889) = k1_relat_1(C_1889)
      | ~ m1_subset_1(C_1889,k1_zfmisc_1(k2_zfmisc_1(A_1887,B_1888))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32802,plain,(
    ! [B_1896,C_1897] :
      ( k1_relset_1('#skF_1',B_1896,C_1897) = k1_relat_1(C_1897)
      | ~ m1_subset_1(C_1897,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32630,c_32755])).

tff(c_32811,plain,(
    ! [B_1896] : k1_relset_1('#skF_1',B_1896,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_32608,c_32802])).

tff(c_32617,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32603,c_66])).

tff(c_32605,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32603,c_31235])).

tff(c_33065,plain,(
    ! [B_1924,C_1925] :
      ( k1_relset_1('#skF_1',B_1924,C_1925) = '#skF_1'
      | ~ v1_funct_2(C_1925,'#skF_1',B_1924)
      | ~ m1_subset_1(C_1925,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32605,c_32605,c_32605,c_32605,c_70])).

tff(c_33070,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32617,c_33065])).

tff(c_33077,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32608,c_32811,c_33070])).

tff(c_32645,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32603,c_32603,c_31242])).

tff(c_32613,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32603,c_25126])).

tff(c_32700,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32645,c_32613])).

tff(c_32901,plain,(
    ! [A_1908,B_1909,C_1910] :
      ( k2_relset_1(A_1908,B_1909,C_1910) = k2_relat_1(C_1910)
      | ~ m1_subset_1(C_1910,k1_zfmisc_1(k2_zfmisc_1(A_1908,B_1909))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32952,plain,(
    ! [B_1917,C_1918] :
      ( k2_relset_1('#skF_1',B_1917,C_1918) = k2_relat_1(C_1918)
      | ~ m1_subset_1(C_1918,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32630,c_32901])).

tff(c_32960,plain,(
    ! [B_1917] : k2_relset_1('#skF_1',B_1917,k2_funct_1('#skF_1')) = k2_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32700,c_32952])).

tff(c_33240,plain,(
    ! [A_1940,B_1941,C_1942] :
      ( m1_subset_1(k2_relset_1(A_1940,B_1941,C_1942),k1_zfmisc_1(B_1941))
      | ~ m1_subset_1(C_1942,k1_zfmisc_1(k2_zfmisc_1(A_1940,B_1941))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_33277,plain,(
    ! [B_1917] :
      ( m1_subset_1(k2_relat_1(k2_funct_1('#skF_1')),k1_zfmisc_1(B_1917))
      | ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_1917))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32960,c_33240])).

tff(c_33498,plain,(
    ! [B_1949] : m1_subset_1(k2_relat_1(k2_funct_1('#skF_1')),k1_zfmisc_1(B_1949)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32700,c_32630,c_33277])).

tff(c_33535,plain,(
    ! [B_1949] :
      ( m1_subset_1(k1_relat_1('#skF_1'),k1_zfmisc_1(B_1949))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_33498])).

tff(c_33584,plain,(
    ! [B_1952] : m1_subset_1('#skF_1',k1_zfmisc_1(B_1952)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32611,c_32619,c_32618,c_33077,c_33535])).

tff(c_33638,plain,(
    ! [B_1952] : r1_tarski('#skF_1',B_1952) ),
    inference(resolution,[status(thm)],[c_33584,c_14])).

tff(c_32604,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_31248])).

tff(c_32624,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32603,c_32604])).

tff(c_32971,plain,(
    ! [B_1921] : k2_relset_1('#skF_1',B_1921,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_32608,c_32952])).

tff(c_32616,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32603,c_60])).

tff(c_32978,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_32971,c_32616])).

tff(c_32917,plain,(
    ! [A_1911,C_1912] :
      ( k2_relset_1(A_1911,'#skF_1',C_1912) = k2_relat_1(C_1912)
      | ~ m1_subset_1(C_1912,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32645,c_32901])).

tff(c_32926,plain,(
    ! [A_1911] : k2_relset_1(A_1911,'#skF_1','#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_32608,c_32917])).

tff(c_32991,plain,(
    ! [A_1911] : k2_relset_1(A_1911,'#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32978,c_32926])).

tff(c_33280,plain,(
    ! [A_1911] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_1911,'#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32991,c_33240])).

tff(c_33304,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32608,c_32645,c_33280])).

tff(c_33328,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_33304,c_14])).

tff(c_33341,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_33328,c_2])).

tff(c_33350,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_32624,c_33341])).

tff(c_33643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33638,c_33350])).

tff(c_33644,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_25167])).

tff(c_33707,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33650,c_33658,c_33644])).

tff(c_33748,plain,(
    ! [A_1959] :
      ( k1_relat_1(k2_funct_1(A_1959)) = k2_relat_1(A_1959)
      | ~ v2_funct_1(A_1959)
      | ~ v1_funct_1(A_1959)
      | ~ v1_relat_1(A_1959) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_33760,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_33707,c_33748])).

tff(c_33764,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25159,c_68,c_62,c_33760])).

tff(c_33651,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31235,c_31235,c_10])).

tff(c_33792,plain,(
    ! [A_1961,B_1962,C_1963] :
      ( k2_relset_1(A_1961,B_1962,C_1963) = k2_relat_1(C_1963)
      | ~ m1_subset_1(C_1963,k1_zfmisc_1(k2_zfmisc_1(A_1961,B_1962))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_33826,plain,(
    ! [A_1969,C_1970] :
      ( k2_relset_1(A_1969,'#skF_3',C_1970) = k2_relat_1(C_1970)
      | ~ m1_subset_1(C_1970,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33651,c_33792])).

tff(c_33828,plain,(
    ! [A_1969] : k2_relset_1(A_1969,'#skF_3','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30089,c_33826])).

tff(c_33835,plain,(
    ! [A_1971] : k2_relset_1(A_1971,'#skF_3','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33764,c_33828])).

tff(c_33663,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33658,c_33658,c_60])).

tff(c_33842,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_33835,c_33663])).

tff(c_33804,plain,(
    ! [B_1964,C_1965] :
      ( k2_relset_1('#skF_3',B_1964,C_1965) = k2_relat_1(C_1965)
      | ~ m1_subset_1(C_1965,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33650,c_33792])).

tff(c_33806,plain,(
    ! [B_1964] : k2_relset_1('#skF_3',B_1964,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30089,c_33804])).

tff(c_33811,plain,(
    ! [B_1964] : k2_relset_1('#skF_3',B_1964,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33764,c_33806])).

tff(c_33867,plain,(
    ! [B_1964] : k2_relset_1('#skF_3',B_1964,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33842,c_33811])).

tff(c_34107,plain,(
    ! [A_2001,B_2002,C_2003] :
      ( m1_subset_1(k2_relset_1(A_2001,B_2002,C_2003),k1_zfmisc_1(B_2002))
      | ~ m1_subset_1(C_2003,k1_zfmisc_1(k2_zfmisc_1(A_2001,B_2002))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34147,plain,(
    ! [B_1964] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(B_1964))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_1964))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33867,c_34107])).

tff(c_34167,plain,(
    ! [B_2004] : m1_subset_1('#skF_3',k1_zfmisc_1(B_2004)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30089,c_33650,c_34147])).

tff(c_34215,plain,(
    ! [B_2004] : r1_tarski('#skF_3',B_2004) ),
    inference(resolution,[status(thm)],[c_34167,c_14])).

tff(c_33869,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33842,c_33764])).

tff(c_33975,plain,(
    ! [B_1985,A_1986] :
      ( v1_funct_2(B_1985,k1_relat_1(B_1985),A_1986)
      | ~ r1_tarski(k2_relat_1(B_1985),A_1986)
      | ~ v1_funct_1(B_1985)
      | ~ v1_relat_1(B_1985) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_33978,plain,(
    ! [A_1986] :
      ( v1_funct_2('#skF_3','#skF_3',A_1986)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_1986)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33842,c_33975])).

tff(c_33984,plain,(
    ! [A_1987] :
      ( v1_funct_2('#skF_3','#skF_3',A_1987)
      | ~ r1_tarski('#skF_3',A_1987) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25159,c_68,c_33869,c_33978])).

tff(c_33662,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33658,c_25125])).

tff(c_33730,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33707,c_33662])).

tff(c_33988,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_33984,c_33730])).

tff(c_34220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34215,c_33988])).

tff(c_34221,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_33657])).

tff(c_34222,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_33657])).

tff(c_34242,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34221,c_34222])).

tff(c_34226,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34221,c_34221,c_30089])).

tff(c_34223,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34221,c_31235])).

tff(c_34287,plain,(
    ! [A_21] :
      ( v1_funct_2('#skF_1',A_21,'#skF_1')
      | A_21 = '#skF_1'
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34223,c_34223,c_34223,c_34223,c_34223,c_71])).

tff(c_34288,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_34287])).

tff(c_34295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34226,c_34288])).

tff(c_34375,plain,(
    ! [A_2011] :
      ( v1_funct_2('#skF_1',A_2011,'#skF_1')
      | A_2011 = '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_34287])).

tff(c_34248,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34221,c_34221,c_33651])).

tff(c_34308,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34221,c_34248,c_33644])).

tff(c_34232,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34221,c_25125])).

tff(c_34327,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34308,c_34232])).

tff(c_34378,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34375,c_34327])).

tff(c_34382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34242,c_34378])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:34:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.32/4.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.73/4.70  
% 11.73/4.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.73/4.71  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.73/4.71  
% 11.73/4.71  %Foreground sorts:
% 11.73/4.71  
% 11.73/4.71  
% 11.73/4.71  %Background operators:
% 11.73/4.71  
% 11.73/4.71  
% 11.73/4.71  %Foreground operators:
% 11.73/4.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.73/4.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.73/4.71  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.73/4.71  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.73/4.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.73/4.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.73/4.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.73/4.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.73/4.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.73/4.71  tff('#skF_2', type, '#skF_2': $i).
% 11.73/4.71  tff('#skF_3', type, '#skF_3': $i).
% 11.73/4.71  tff('#skF_1', type, '#skF_1': $i).
% 11.73/4.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.73/4.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.73/4.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.73/4.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.73/4.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.73/4.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.73/4.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.73/4.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.73/4.71  
% 11.85/4.76  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.85/4.76  tff(f_132, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 11.85/4.76  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.85/4.76  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.85/4.76  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.85/4.76  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 11.85/4.76  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.85/4.76  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.85/4.76  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 11.85/4.76  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.85/4.76  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.85/4.76  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 11.85/4.76  tff(f_115, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 11.85/4.76  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.85/4.76  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.85/4.76  tff(c_103, plain, (![A_32]: (v1_funct_1(k2_funct_1(A_32)) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.85/4.76  tff(c_58, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.85/4.76  tff(c_102, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_58])).
% 11.85/4.76  tff(c_106, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_102])).
% 11.85/4.76  tff(c_109, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_106])).
% 11.85/4.76  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.85/4.76  tff(c_131, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.85/4.76  tff(c_138, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_131])).
% 11.85/4.76  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_138])).
% 11.85/4.76  tff(c_148, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_58])).
% 11.85/4.76  tff(c_150, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_148])).
% 11.85/4.76  tff(c_166, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.85/4.76  tff(c_179, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_166])).
% 11.85/4.76  tff(c_62, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.85/4.76  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.85/4.76  tff(c_430, plain, (![A_85, B_86, C_87]: (k2_relset_1(A_85, B_86, C_87)=k2_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.85/4.76  tff(c_440, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_430])).
% 11.85/4.76  tff(c_450, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_440])).
% 11.85/4.76  tff(c_24, plain, (![A_8]: (k1_relat_1(k2_funct_1(A_8))=k2_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.85/4.76  tff(c_20, plain, (![A_7]: (v1_relat_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.85/4.76  tff(c_149, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_58])).
% 11.85/4.76  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.85/4.76  tff(c_282, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.85/4.76  tff(c_297, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_282])).
% 11.85/4.76  tff(c_7901, plain, (![B_477, A_478, C_479]: (k1_xboole_0=B_477 | k1_relset_1(A_478, B_477, C_479)=A_478 | ~v1_funct_2(C_479, A_478, B_477) | ~m1_subset_1(C_479, k1_zfmisc_1(k2_zfmisc_1(A_478, B_477))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.85/4.76  tff(c_7929, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_7901])).
% 11.85/4.76  tff(c_7947, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_297, c_7929])).
% 11.85/4.76  tff(c_7949, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_7947])).
% 11.85/4.76  tff(c_270, plain, (![A_62]: (k2_relat_1(k2_funct_1(A_62))=k1_relat_1(A_62) | ~v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.85/4.76  tff(c_48, plain, (![A_24]: (v1_funct_2(A_24, k1_relat_1(A_24), k2_relat_1(A_24)) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.85/4.76  tff(c_11312, plain, (![A_662]: (v1_funct_2(k2_funct_1(A_662), k1_relat_1(k2_funct_1(A_662)), k1_relat_1(A_662)) | ~v1_funct_1(k2_funct_1(A_662)) | ~v1_relat_1(k2_funct_1(A_662)) | ~v2_funct_1(A_662) | ~v1_funct_1(A_662) | ~v1_relat_1(A_662))), inference(superposition, [status(thm), theory('equality')], [c_270, c_48])).
% 11.85/4.76  tff(c_11315, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7949, c_11312])).
% 11.85/4.76  tff(c_11326, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_149, c_11315])).
% 11.85/4.76  tff(c_11329, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_11326])).
% 11.85/4.76  tff(c_11332, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_11329])).
% 11.85/4.76  tff(c_11336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_11332])).
% 11.85/4.76  tff(c_11338, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_11326])).
% 11.85/4.76  tff(c_22, plain, (![A_8]: (k2_relat_1(k2_funct_1(A_8))=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.85/4.76  tff(c_317, plain, (![A_69]: (m1_subset_1(A_69, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_69), k2_relat_1(A_69)))) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.85/4.76  tff(c_12244, plain, (![A_692]: (m1_subset_1(k2_funct_1(A_692), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_692)), k1_relat_1(A_692)))) | ~v1_funct_1(k2_funct_1(A_692)) | ~v1_relat_1(k2_funct_1(A_692)) | ~v2_funct_1(A_692) | ~v1_funct_1(A_692) | ~v1_relat_1(A_692))), inference(superposition, [status(thm), theory('equality')], [c_22, c_317])).
% 11.85/4.76  tff(c_12267, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7949, c_12244])).
% 11.85/4.76  tff(c_12285, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_11338, c_149, c_12267])).
% 11.85/4.76  tff(c_12310, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_12285])).
% 11.85/4.76  tff(c_12323, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_450, c_12310])).
% 11.85/4.76  tff(c_12325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_12323])).
% 11.85/4.76  tff(c_12326, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_7947])).
% 11.85/4.76  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.85/4.76  tff(c_12361, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12326, c_12326, c_10])).
% 11.85/4.76  tff(c_12401, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12361, c_64])).
% 11.85/4.76  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.85/4.76  tff(c_12360, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12326, c_12326, c_12])).
% 11.85/4.76  tff(c_153, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | ~m1_subset_1(A_43, k1_zfmisc_1(B_44)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.85/4.76  tff(c_161, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_153])).
% 11.85/4.76  tff(c_12400, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12361, c_161])).
% 11.85/4.76  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.85/4.76  tff(c_7486, plain, (![B_455, C_456]: (k2_relset_1(k1_xboole_0, B_455, C_456)=k2_relat_1(C_456) | ~m1_subset_1(C_456, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_430])).
% 11.85/4.76  tff(c_7493, plain, (![B_455, A_5]: (k2_relset_1(k1_xboole_0, B_455, A_5)=k2_relat_1(A_5) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_7486])).
% 11.85/4.76  tff(c_12921, plain, (![B_731, A_732]: (k2_relset_1('#skF_2', B_731, A_732)=k2_relat_1(A_732) | ~r1_tarski(A_732, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12326, c_12326, c_7493])).
% 11.85/4.76  tff(c_12926, plain, (![B_731]: (k2_relset_1('#skF_2', B_731, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_12400, c_12921])).
% 11.85/4.76  tff(c_12936, plain, (![B_733]: (k2_relset_1('#skF_2', B_733, '#skF_3')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_450, c_12926])).
% 11.85/4.76  tff(c_28, plain, (![A_12, B_13, C_14]: (m1_subset_1(k2_relset_1(A_12, B_13, C_14), k1_zfmisc_1(B_13)) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.85/4.76  tff(c_12948, plain, (![B_733]: (m1_subset_1('#skF_2', k1_zfmisc_1(B_733)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_733))))), inference(superposition, [status(thm), theory('equality')], [c_12936, c_28])).
% 11.85/4.76  tff(c_12963, plain, (![B_734]: (m1_subset_1('#skF_2', k1_zfmisc_1(B_734)))), inference(demodulation, [status(thm), theory('equality')], [c_12401, c_12360, c_12948])).
% 11.85/4.76  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.85/4.76  tff(c_13010, plain, (![B_734]: (r1_tarski('#skF_2', B_734))), inference(resolution, [status(thm)], [c_12963, c_14])).
% 11.85/4.76  tff(c_214, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(B_55, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.85/4.76  tff(c_219, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_161, c_214])).
% 11.85/4.76  tff(c_235, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_219])).
% 11.85/4.76  tff(c_12399, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12361, c_235])).
% 11.85/4.76  tff(c_13013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13010, c_12399])).
% 11.85/4.76  tff(c_13014, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_219])).
% 11.85/4.76  tff(c_13018, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_13014, c_64])).
% 11.85/4.76  tff(c_13263, plain, (![A_763, B_764, C_765]: (k2_relset_1(A_763, B_764, C_765)=k2_relat_1(C_765) | ~m1_subset_1(C_765, k1_zfmisc_1(k2_zfmisc_1(A_763, B_764))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.85/4.76  tff(c_13318, plain, (![C_775]: (k2_relset_1('#skF_1', '#skF_2', C_775)=k2_relat_1(C_775) | ~m1_subset_1(C_775, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_13014, c_13263])).
% 11.85/4.76  tff(c_13321, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_13018, c_13318])).
% 11.85/4.76  tff(c_13327, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_13321])).
% 11.85/4.76  tff(c_13080, plain, (![A_739]: (k1_relat_1(k2_funct_1(A_739))=k2_relat_1(A_739) | ~v2_funct_1(A_739) | ~v1_funct_1(A_739) | ~v1_relat_1(A_739))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.85/4.76  tff(c_17863, plain, (![A_994]: (v1_funct_2(k2_funct_1(A_994), k2_relat_1(A_994), k2_relat_1(k2_funct_1(A_994))) | ~v1_funct_1(k2_funct_1(A_994)) | ~v1_relat_1(k2_funct_1(A_994)) | ~v2_funct_1(A_994) | ~v1_funct_1(A_994) | ~v1_relat_1(A_994))), inference(superposition, [status(thm), theory('equality')], [c_13080, c_48])).
% 11.85/4.76  tff(c_17875, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13327, c_17863])).
% 11.85/4.76  tff(c_17887, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_149, c_17875])).
% 11.85/4.76  tff(c_17888, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_17887])).
% 11.85/4.76  tff(c_17891, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_17888])).
% 11.85/4.76  tff(c_17895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_17891])).
% 11.85/4.76  tff(c_17897, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_17887])).
% 11.85/4.76  tff(c_13104, plain, (![A_741, B_742, C_743]: (k1_relset_1(A_741, B_742, C_743)=k1_relat_1(C_743) | ~m1_subset_1(C_743, k1_zfmisc_1(k2_zfmisc_1(A_741, B_742))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.85/4.76  tff(c_13188, plain, (![C_755]: (k1_relset_1('#skF_1', '#skF_2', C_755)=k1_relat_1(C_755) | ~m1_subset_1(C_755, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_13014, c_13104])).
% 11.85/4.76  tff(c_13196, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_13018, c_13188])).
% 11.85/4.76  tff(c_13991, plain, (![B_803, C_804, A_805]: (k1_xboole_0=B_803 | v1_funct_2(C_804, A_805, B_803) | k1_relset_1(A_805, B_803, C_804)!=A_805 | ~m1_subset_1(C_804, k1_zfmisc_1(k2_zfmisc_1(A_805, B_803))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.85/4.76  tff(c_14011, plain, (![C_804]: (k1_xboole_0='#skF_2' | v1_funct_2(C_804, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_804)!='#skF_1' | ~m1_subset_1(C_804, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_13014, c_13991])).
% 11.85/4.76  tff(c_14035, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_14011])).
% 11.85/4.76  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.85/4.76  tff(c_13023, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_13014, c_8])).
% 11.85/4.76  tff(c_13047, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_13023])).
% 11.85/4.76  tff(c_14062, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14035, c_13047])).
% 11.85/4.76  tff(c_14139, plain, (![A_810]: (k2_zfmisc_1(A_810, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14035, c_14035, c_10])).
% 11.85/4.76  tff(c_14165, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_14139, c_13014])).
% 11.85/4.76  tff(c_14184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14062, c_14165])).
% 11.85/4.76  tff(c_14186, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_14011])).
% 11.85/4.76  tff(c_14297, plain, (![B_821, A_822, C_823]: (k1_xboole_0=B_821 | k1_relset_1(A_822, B_821, C_823)=A_822 | ~v1_funct_2(C_823, A_822, B_821) | ~m1_subset_1(C_823, k1_zfmisc_1(k2_zfmisc_1(A_822, B_821))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.85/4.76  tff(c_14317, plain, (![C_823]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_823)='#skF_1' | ~v1_funct_2(C_823, '#skF_1', '#skF_2') | ~m1_subset_1(C_823, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_13014, c_14297])).
% 11.85/4.76  tff(c_14358, plain, (![C_826]: (k1_relset_1('#skF_1', '#skF_2', C_826)='#skF_1' | ~v1_funct_2(C_826, '#skF_1', '#skF_2') | ~m1_subset_1(C_826, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_14186, c_14317])).
% 11.85/4.76  tff(c_14369, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_13018, c_14358])).
% 11.85/4.76  tff(c_14379, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_13196, c_14369])).
% 11.85/4.76  tff(c_13163, plain, (![A_752]: (m1_subset_1(A_752, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_752), k2_relat_1(A_752)))) | ~v1_funct_1(A_752) | ~v1_relat_1(A_752))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.85/4.76  tff(c_18896, plain, (![A_1038]: (m1_subset_1(k2_funct_1(A_1038), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1038)), k1_relat_1(A_1038)))) | ~v1_funct_1(k2_funct_1(A_1038)) | ~v1_relat_1(k2_funct_1(A_1038)) | ~v2_funct_1(A_1038) | ~v1_funct_1(A_1038) | ~v1_relat_1(A_1038))), inference(superposition, [status(thm), theory('equality')], [c_22, c_13163])).
% 11.85/4.76  tff(c_18919, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14379, c_18896])).
% 11.85/4.76  tff(c_18934, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_17897, c_149, c_18919])).
% 11.85/4.76  tff(c_18957, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_18934])).
% 11.85/4.76  tff(c_18970, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_13327, c_18957])).
% 11.85/4.76  tff(c_18972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_18970])).
% 11.85/4.76  tff(c_18974, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_13023])).
% 11.85/4.76  tff(c_18979, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18974, c_18974, c_12])).
% 11.85/4.76  tff(c_18973, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_13023])).
% 11.85/4.76  tff(c_18986, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18974, c_18974, c_18973])).
% 11.85/4.76  tff(c_18987, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_18986])).
% 11.85/4.76  tff(c_19001, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18987, c_150])).
% 11.85/4.76  tff(c_19053, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18979, c_19001])).
% 11.85/4.76  tff(c_18980, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18974, c_18974, c_10])).
% 11.85/4.76  tff(c_19198, plain, (![A_1067, B_1068, C_1069]: (k2_relset_1(A_1067, B_1068, C_1069)=k2_relat_1(C_1069) | ~m1_subset_1(C_1069, k1_zfmisc_1(k2_zfmisc_1(A_1067, B_1068))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.85/4.76  tff(c_19254, plain, (![A_1076, C_1077]: (k2_relset_1(A_1076, '#skF_3', C_1077)=k2_relat_1(C_1077) | ~m1_subset_1(C_1077, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_18980, c_19198])).
% 11.85/4.76  tff(c_19262, plain, (![A_1078]: (k2_relset_1(A_1078, '#skF_3', '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_13018, c_19254])).
% 11.85/4.76  tff(c_19002, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18987, c_18987, c_60])).
% 11.85/4.76  tff(c_19269, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_19262, c_19002])).
% 11.85/4.76  tff(c_19915, plain, (![B_1127, A_1128]: (m1_subset_1(B_1127, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1127), A_1128))) | ~r1_tarski(k2_relat_1(B_1127), A_1128) | ~v1_funct_1(B_1127) | ~v1_relat_1(B_1127))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.85/4.76  tff(c_19381, plain, (![A_1089, B_1090, C_1091]: (m1_subset_1(k2_relset_1(A_1089, B_1090, C_1091), k1_zfmisc_1(B_1090)) | ~m1_subset_1(C_1091, k1_zfmisc_1(k2_zfmisc_1(A_1089, B_1090))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.85/4.76  tff(c_19432, plain, (![A_1089, B_1090, C_1091]: (r1_tarski(k2_relset_1(A_1089, B_1090, C_1091), B_1090) | ~m1_subset_1(C_1091, k1_zfmisc_1(k2_zfmisc_1(A_1089, B_1090))))), inference(resolution, [status(thm)], [c_19381, c_14])).
% 11.85/4.76  tff(c_20686, plain, (![B_1189, A_1190]: (r1_tarski(k2_relset_1(k1_relat_1(B_1189), A_1190, B_1189), A_1190) | ~r1_tarski(k2_relat_1(B_1189), A_1190) | ~v1_funct_1(B_1189) | ~v1_relat_1(B_1189))), inference(resolution, [status(thm)], [c_19915, c_19432])).
% 11.85/4.76  tff(c_178, plain, (![A_5, A_46, B_47]: (v1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_46, B_47)))), inference(resolution, [status(thm)], [c_16, c_166])).
% 11.85/4.76  tff(c_13027, plain, (![A_5]: (v1_relat_1(A_5) | ~r1_tarski(A_5, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_13014, c_178])).
% 11.85/4.76  tff(c_20759, plain, (![B_1191]: (v1_relat_1(k2_relset_1(k1_relat_1(B_1191), '#skF_3', B_1191)) | ~r1_tarski(k2_relat_1(B_1191), '#skF_3') | ~v1_funct_1(B_1191) | ~v1_relat_1(B_1191))), inference(resolution, [status(thm)], [c_20686, c_13027])).
% 11.85/4.76  tff(c_21152, plain, (![A_1209]: (v1_relat_1(k2_relset_1(k2_relat_1(A_1209), '#skF_3', k2_funct_1(A_1209))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_1209)), '#skF_3') | ~v1_funct_1(k2_funct_1(A_1209)) | ~v1_relat_1(k2_funct_1(A_1209)) | ~v2_funct_1(A_1209) | ~v1_funct_1(A_1209) | ~v1_relat_1(A_1209))), inference(superposition, [status(thm), theory('equality')], [c_24, c_20759])).
% 11.85/4.76  tff(c_21155, plain, (v1_relat_1(k2_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_3'))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_19269, c_21152])).
% 11.85/4.76  tff(c_21160, plain, (v1_relat_1(k2_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_3'))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_149, c_21155])).
% 11.85/4.76  tff(c_21271, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_21160])).
% 11.85/4.76  tff(c_21274, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_21271])).
% 11.85/4.76  tff(c_21278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_21274])).
% 11.85/4.76  tff(c_21280, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_21160])).
% 11.85/4.76  tff(c_19218, plain, (![A_1072]: (m1_subset_1(A_1072, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1072), k2_relat_1(A_1072)))) | ~v1_funct_1(A_1072) | ~v1_relat_1(A_1072))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.85/4.76  tff(c_21998, plain, (![A_1242]: (m1_subset_1(k2_funct_1(A_1242), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1242), k2_relat_1(k2_funct_1(A_1242))))) | ~v1_funct_1(k2_funct_1(A_1242)) | ~v1_relat_1(k2_funct_1(A_1242)) | ~v2_funct_1(A_1242) | ~v1_funct_1(A_1242) | ~v1_relat_1(A_1242))), inference(superposition, [status(thm), theory('equality')], [c_24, c_19218])).
% 11.85/4.76  tff(c_22024, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_19269, c_21998])).
% 11.85/4.76  tff(c_22040, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_21280, c_149, c_18979, c_22024])).
% 11.85/4.76  tff(c_22042, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19053, c_22040])).
% 11.85/4.76  tff(c_22043, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_18986])).
% 11.85/4.76  tff(c_22071, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22043, c_22043, c_18980])).
% 11.85/4.76  tff(c_22051, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22043, c_150])).
% 11.85/4.76  tff(c_22150, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22071, c_22051])).
% 11.85/4.76  tff(c_22050, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22043, c_179])).
% 11.85/4.76  tff(c_22056, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22043, c_68])).
% 11.85/4.76  tff(c_22055, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22043, c_62])).
% 11.85/4.76  tff(c_22052, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22043, c_149])).
% 11.85/4.76  tff(c_22047, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22043, c_22043, c_13018])).
% 11.85/4.76  tff(c_22089, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22043, c_22043, c_18979])).
% 11.85/4.76  tff(c_22179, plain, (![A_1252, B_1253, C_1254]: (k2_relset_1(A_1252, B_1253, C_1254)=k2_relat_1(C_1254) | ~m1_subset_1(C_1254, k1_zfmisc_1(k2_zfmisc_1(A_1252, B_1253))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.85/4.76  tff(c_22191, plain, (![B_1255, C_1256]: (k2_relset_1('#skF_1', B_1255, C_1256)=k2_relat_1(C_1256) | ~m1_subset_1(C_1256, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_22089, c_22179])).
% 11.85/4.76  tff(c_22199, plain, (![B_1257]: (k2_relset_1('#skF_1', B_1257, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_22047, c_22191])).
% 11.85/4.76  tff(c_22053, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22043, c_60])).
% 11.85/4.76  tff(c_22203, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_22199, c_22053])).
% 11.85/4.76  tff(c_22137, plain, (![A_1248]: (k1_relat_1(k2_funct_1(A_1248))=k2_relat_1(A_1248) | ~v2_funct_1(A_1248) | ~v1_funct_1(A_1248) | ~v1_relat_1(A_1248))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.85/4.76  tff(c_24822, plain, (![A_1428]: (v1_funct_2(k2_funct_1(A_1428), k2_relat_1(A_1428), k2_relat_1(k2_funct_1(A_1428))) | ~v1_funct_1(k2_funct_1(A_1428)) | ~v1_relat_1(k2_funct_1(A_1428)) | ~v2_funct_1(A_1428) | ~v1_funct_1(A_1428) | ~v1_relat_1(A_1428))), inference(superposition, [status(thm), theory('equality')], [c_22137, c_48])).
% 11.85/4.76  tff(c_24831, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', k2_relat_1(k2_funct_1('#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22203, c_24822])).
% 11.85/4.76  tff(c_24843, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', k2_relat_1(k2_funct_1('#skF_1'))) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22050, c_22056, c_22055, c_22052, c_24831])).
% 11.85/4.76  tff(c_24844, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_24843])).
% 11.85/4.76  tff(c_24847, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_24844])).
% 11.85/4.76  tff(c_24851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22050, c_22056, c_24847])).
% 11.85/4.76  tff(c_24853, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_24843])).
% 11.85/4.76  tff(c_22044, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_18986])).
% 11.85/4.76  tff(c_22061, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22043, c_22044])).
% 11.85/4.76  tff(c_22210, plain, (![A_1258, B_1259, C_1260]: (k1_relset_1(A_1258, B_1259, C_1260)=k1_relat_1(C_1260) | ~m1_subset_1(C_1260, k1_zfmisc_1(k2_zfmisc_1(A_1258, B_1259))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.85/4.76  tff(c_22277, plain, (![B_1269, C_1270]: (k1_relset_1('#skF_1', B_1269, C_1270)=k1_relat_1(C_1270) | ~m1_subset_1(C_1270, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_22089, c_22210])).
% 11.85/4.76  tff(c_22283, plain, (![B_1269]: (k1_relset_1('#skF_1', B_1269, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_22047, c_22277])).
% 11.85/4.76  tff(c_22054, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22043, c_66])).
% 11.85/4.76  tff(c_22045, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22043, c_18974])).
% 11.85/4.76  tff(c_42, plain, (![B_22, C_23]: (k1_relset_1(k1_xboole_0, B_22, C_23)=k1_xboole_0 | ~v1_funct_2(C_23, k1_xboole_0, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_22))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.85/4.76  tff(c_70, plain, (![B_22, C_23]: (k1_relset_1(k1_xboole_0, B_22, C_23)=k1_xboole_0 | ~v1_funct_2(C_23, k1_xboole_0, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_42])).
% 11.85/4.76  tff(c_22534, plain, (![B_1295, C_1296]: (k1_relset_1('#skF_1', B_1295, C_1296)='#skF_1' | ~v1_funct_2(C_1296, '#skF_1', B_1295) | ~m1_subset_1(C_1296, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22045, c_22045, c_22045, c_22045, c_70])).
% 11.85/4.76  tff(c_22536, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_22054, c_22534])).
% 11.85/4.76  tff(c_22542, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22047, c_22283, c_22536])).
% 11.85/4.76  tff(c_22285, plain, (![A_1271]: (m1_subset_1(A_1271, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1271), k2_relat_1(A_1271)))) | ~v1_funct_1(A_1271) | ~v1_relat_1(A_1271))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.85/4.76  tff(c_22300, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_2'))) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22203, c_22285])).
% 11.85/4.76  tff(c_22312, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22050, c_22056, c_22300])).
% 11.85/4.76  tff(c_22337, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_22312, c_14])).
% 11.85/4.76  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.85/4.76  tff(c_22347, plain, (k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_2')='#skF_1' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_22337, c_2])).
% 11.85/4.76  tff(c_22448, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_22347])).
% 11.85/4.76  tff(c_22547, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22542, c_22448])).
% 11.85/4.76  tff(c_22557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_22089, c_22547])).
% 11.85/4.76  tff(c_22558, plain, (k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_22347])).
% 11.85/4.76  tff(c_18975, plain, (![B_4, A_3]: (B_4='#skF_3' | A_3='#skF_3' | k2_zfmisc_1(A_3, B_4)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18974, c_18974, c_18974, c_8])).
% 11.85/4.76  tff(c_22155, plain, (![B_4, A_3]: (B_4='#skF_1' | A_3='#skF_1' | k2_zfmisc_1(A_3, B_4)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22043, c_22043, c_22043, c_18975])).
% 11.85/4.76  tff(c_22582, plain, ('#skF_2'='#skF_1' | k1_relat_1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_22558, c_22155])).
% 11.85/4.76  tff(c_22594, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_22061, c_22582])).
% 11.85/4.76  tff(c_25084, plain, (![A_1440]: (m1_subset_1(k2_funct_1(A_1440), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1440)), k1_relat_1(A_1440)))) | ~v1_funct_1(k2_funct_1(A_1440)) | ~v1_relat_1(k2_funct_1(A_1440)) | ~v2_funct_1(A_1440) | ~v1_funct_1(A_1440) | ~v1_relat_1(A_1440))), inference(superposition, [status(thm), theory('equality')], [c_22, c_22285])).
% 11.85/4.76  tff(c_25107, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22594, c_25084])).
% 11.85/4.76  tff(c_25122, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22050, c_22056, c_22055, c_24853, c_22052, c_22071, c_25107])).
% 11.85/4.76  tff(c_25124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22150, c_25122])).
% 11.85/4.76  tff(c_25125, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_148])).
% 11.85/4.76  tff(c_25142, plain, (![C_1445, A_1446, B_1447]: (v1_relat_1(C_1445) | ~m1_subset_1(C_1445, k1_zfmisc_1(k2_zfmisc_1(A_1446, B_1447))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.85/4.76  tff(c_25159, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_25142])).
% 11.85/4.76  tff(c_26912, plain, (![A_1544, B_1545, C_1546]: (k2_relset_1(A_1544, B_1545, C_1546)=k2_relat_1(C_1546) | ~m1_subset_1(C_1546, k1_zfmisc_1(k2_zfmisc_1(A_1544, B_1545))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.85/4.76  tff(c_26922, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_26912])).
% 11.85/4.76  tff(c_26931, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_26922])).
% 11.85/4.76  tff(c_25126, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_148])).
% 11.85/4.76  tff(c_25157, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_25126, c_25142])).
% 11.85/4.76  tff(c_27131, plain, (![A_1566, B_1567, C_1568]: (k1_relset_1(A_1566, B_1567, C_1568)=k1_relat_1(C_1568) | ~m1_subset_1(C_1568, k1_zfmisc_1(k2_zfmisc_1(A_1566, B_1567))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.85/4.76  tff(c_27157, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_27131])).
% 11.85/4.76  tff(c_28150, plain, (![B_1623, A_1624, C_1625]: (k1_xboole_0=B_1623 | k1_relset_1(A_1624, B_1623, C_1625)=A_1624 | ~v1_funct_2(C_1625, A_1624, B_1623) | ~m1_subset_1(C_1625, k1_zfmisc_1(k2_zfmisc_1(A_1624, B_1623))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.85/4.76  tff(c_28177, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_28150])).
% 11.85/4.76  tff(c_28196, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_27157, c_28177])).
% 11.85/4.76  tff(c_28198, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_28196])).
% 11.85/4.76  tff(c_25432, plain, (![A_1485, B_1486, C_1487]: (k2_relset_1(A_1485, B_1486, C_1487)=k2_relat_1(C_1487) | ~m1_subset_1(C_1487, k1_zfmisc_1(k2_zfmisc_1(A_1485, B_1486))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.85/4.76  tff(c_25445, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_25432])).
% 11.85/4.76  tff(c_25456, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_25445])).
% 11.85/4.76  tff(c_25300, plain, (![A_1465, B_1466, C_1467]: (k1_relset_1(A_1465, B_1466, C_1467)=k1_relat_1(C_1467) | ~m1_subset_1(C_1467, k1_zfmisc_1(k2_zfmisc_1(A_1465, B_1466))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.85/4.76  tff(c_25321, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_25126, c_25300])).
% 11.85/4.76  tff(c_25932, plain, (![B_1514, C_1515, A_1516]: (k1_xboole_0=B_1514 | v1_funct_2(C_1515, A_1516, B_1514) | k1_relset_1(A_1516, B_1514, C_1515)!=A_1516 | ~m1_subset_1(C_1515, k1_zfmisc_1(k2_zfmisc_1(A_1516, B_1514))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.85/4.76  tff(c_25952, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_25126, c_25932])).
% 11.85/4.76  tff(c_25975, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_25321, c_25952])).
% 11.85/4.76  tff(c_25976, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_25125, c_25975])).
% 11.85/4.76  tff(c_25981, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_25976])).
% 11.85/4.76  tff(c_25984, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_25981])).
% 11.85/4.76  tff(c_25987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25159, c_68, c_62, c_25456, c_25984])).
% 11.85/4.76  tff(c_25988, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_25976])).
% 11.85/4.76  tff(c_26021, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25988, c_25988, c_12])).
% 11.85/4.76  tff(c_26144, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26021, c_64])).
% 11.85/4.76  tff(c_25323, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_25300])).
% 11.85/4.76  tff(c_44, plain, (![B_22, A_21, C_23]: (k1_xboole_0=B_22 | k1_relset_1(A_21, B_22, C_23)=A_21 | ~v1_funct_2(C_23, A_21, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.85/4.76  tff(c_26107, plain, (![B_1518, A_1519, C_1520]: (B_1518='#skF_1' | k1_relset_1(A_1519, B_1518, C_1520)=A_1519 | ~v1_funct_2(C_1520, A_1519, B_1518) | ~m1_subset_1(C_1520, k1_zfmisc_1(k2_zfmisc_1(A_1519, B_1518))))), inference(demodulation, [status(thm), theory('equality')], [c_25988, c_44])).
% 11.85/4.76  tff(c_26130, plain, ('#skF_2'='#skF_1' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_26107])).
% 11.85/4.76  tff(c_26141, plain, ('#skF_2'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_25323, c_26130])).
% 11.85/4.76  tff(c_26249, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_26141])).
% 11.85/4.76  tff(c_25453, plain, (k2_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_25126, c_25432])).
% 11.85/4.76  tff(c_25583, plain, (![A_1500, B_1501, C_1502]: (m1_subset_1(k2_relset_1(A_1500, B_1501, C_1502), k1_zfmisc_1(B_1501)) | ~m1_subset_1(C_1502, k1_zfmisc_1(k2_zfmisc_1(A_1500, B_1501))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.85/4.76  tff(c_25626, plain, (m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_25453, c_25583])).
% 11.85/4.76  tff(c_25654, plain, (m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25126, c_25626])).
% 11.85/4.76  tff(c_25802, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_25654, c_14])).
% 11.85/4.76  tff(c_25809, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_25802])).
% 11.85/4.76  tff(c_25812, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25159, c_68, c_62, c_25809])).
% 11.85/4.76  tff(c_25815, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_25812, c_2])).
% 11.85/4.76  tff(c_25834, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_25815])).
% 11.85/4.76  tff(c_26251, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26249, c_25834])).
% 11.85/4.76  tff(c_26264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_26251])).
% 11.85/4.76  tff(c_26265, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_26141])).
% 11.85/4.76  tff(c_26277, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26265, c_25456])).
% 11.85/4.76  tff(c_25448, plain, (![B_4, C_1487]: (k2_relset_1(k1_xboole_0, B_4, C_1487)=k2_relat_1(C_1487) | ~m1_subset_1(C_1487, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_25432])).
% 11.85/4.76  tff(c_26555, plain, (![B_1533, C_1534]: (k2_relset_1('#skF_1', B_1533, C_1534)=k2_relat_1(C_1534) | ~m1_subset_1(C_1534, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_25988, c_25988, c_25448])).
% 11.85/4.76  tff(c_26564, plain, (![B_1533]: (k2_relset_1('#skF_1', B_1533, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_26144, c_26555])).
% 11.85/4.76  tff(c_26590, plain, (![B_1535]: (k2_relset_1('#skF_1', B_1535, '#skF_3')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26277, c_26564])).
% 11.85/4.76  tff(c_26595, plain, (![B_1535]: (m1_subset_1('#skF_1', k1_zfmisc_1(B_1535)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_1535))))), inference(superposition, [status(thm), theory('equality')], [c_26590, c_28])).
% 11.85/4.76  tff(c_26603, plain, (![B_1536]: (m1_subset_1('#skF_1', k1_zfmisc_1(B_1536)))), inference(demodulation, [status(thm), theory('equality')], [c_26144, c_26021, c_26595])).
% 11.85/4.76  tff(c_26639, plain, (![B_1536]: (r1_tarski('#skF_1', B_1536))), inference(resolution, [status(thm)], [c_26603, c_14])).
% 11.85/4.76  tff(c_26022, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25988, c_25988, c_10])).
% 11.85/4.76  tff(c_25129, plain, (![A_1443, B_1444]: (r1_tarski(A_1443, B_1444) | ~m1_subset_1(A_1443, k1_zfmisc_1(B_1444)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.85/4.76  tff(c_25139, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_25126, c_25129])).
% 11.85/4.76  tff(c_25160, plain, (![B_1448, A_1449]: (B_1448=A_1449 | ~r1_tarski(B_1448, A_1449) | ~r1_tarski(A_1449, B_1448))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.85/4.76  tff(c_25167, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_25139, c_25160])).
% 11.85/4.76  tff(c_25235, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_25167])).
% 11.85/4.76  tff(c_26067, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26022, c_25235])).
% 11.85/4.76  tff(c_26648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26639, c_26067])).
% 11.85/4.76  tff(c_26649, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_25815])).
% 11.85/4.76  tff(c_25810, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_25802, c_2])).
% 11.85/4.76  tff(c_26651, plain, (~r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_25810])).
% 11.85/4.76  tff(c_26698, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_26651])).
% 11.85/4.76  tff(c_26701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25159, c_68, c_62, c_6, c_26649, c_26698])).
% 11.85/4.76  tff(c_26702, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_25810])).
% 11.85/4.76  tff(c_26787, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_26702, c_48])).
% 11.85/4.76  tff(c_26800, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25157, c_149, c_26787])).
% 11.85/4.76  tff(c_26828, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_26800])).
% 11.85/4.76  tff(c_26830, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25159, c_68, c_62, c_25456, c_26828])).
% 11.85/4.76  tff(c_26832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25125, c_26830])).
% 11.85/4.76  tff(c_26833, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_25167])).
% 11.85/4.76  tff(c_26846, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26833, c_25126])).
% 11.85/4.76  tff(c_26941, plain, (![C_1547]: (k2_relset_1('#skF_2', '#skF_1', C_1547)=k2_relat_1(C_1547) | ~m1_subset_1(C_1547, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_26833, c_26912])).
% 11.85/4.76  tff(c_26949, plain, (k2_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_26846, c_26941])).
% 11.85/4.76  tff(c_27335, plain, (![A_1590, B_1591, C_1592]: (m1_subset_1(k2_relset_1(A_1590, B_1591, C_1592), k1_zfmisc_1(B_1591)) | ~m1_subset_1(C_1592, k1_zfmisc_1(k2_zfmisc_1(A_1590, B_1591))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.85/4.76  tff(c_27396, plain, (m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_26949, c_27335])).
% 11.85/4.76  tff(c_27424, plain, (m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26846, c_26833, c_27396])).
% 11.85/4.76  tff(c_27458, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_27424])).
% 11.85/4.76  tff(c_27461, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25159, c_68, c_62, c_27458])).
% 11.85/4.76  tff(c_27604, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_27461, c_14])).
% 11.85/4.76  tff(c_27625, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_27604, c_2])).
% 11.85/4.76  tff(c_27673, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_27625])).
% 11.85/4.76  tff(c_28199, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28198, c_27673])).
% 11.85/4.76  tff(c_28211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_28199])).
% 11.85/4.76  tff(c_28212, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_28196])).
% 11.85/4.76  tff(c_26851, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k2_funct_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26833, c_8])).
% 11.85/4.76  tff(c_26876, plain, (k2_funct_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_26851])).
% 11.85/4.76  tff(c_28241, plain, (k2_funct_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28212, c_26876])).
% 11.85/4.76  tff(c_28248, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28212, c_28212, c_12])).
% 11.85/4.76  tff(c_28308, plain, (k2_funct_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28248, c_26833])).
% 11.85/4.76  tff(c_28310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28241, c_28308])).
% 11.85/4.76  tff(c_28311, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_27625])).
% 11.85/4.76  tff(c_27459, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_27424, c_14])).
% 11.85/4.76  tff(c_27631, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_27459, c_2])).
% 11.85/4.76  tff(c_29103, plain, (~r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_27631])).
% 11.85/4.76  tff(c_29106, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_29103])).
% 11.85/4.76  tff(c_29109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25159, c_68, c_62, c_6, c_28311, c_29106])).
% 11.85/4.76  tff(c_29110, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_27631])).
% 11.85/4.76  tff(c_29156, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_29110, c_48])).
% 11.85/4.76  tff(c_29173, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25157, c_149, c_29156])).
% 11.85/4.76  tff(c_29194, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_29173])).
% 11.85/4.76  tff(c_29196, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25159, c_68, c_62, c_26931, c_29194])).
% 11.85/4.76  tff(c_29198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25125, c_29196])).
% 11.85/4.76  tff(c_29199, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_26851])).
% 11.85/4.76  tff(c_29241, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_29199])).
% 11.85/4.76  tff(c_34, plain, (![A_21]: (v1_funct_2(k1_xboole_0, A_21, k1_xboole_0) | k1_xboole_0=A_21 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_21, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.85/4.76  tff(c_71, plain, (![A_21]: (v1_funct_2(k1_xboole_0, A_21, k1_xboole_0) | k1_xboole_0=A_21 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_34])).
% 11.85/4.76  tff(c_25225, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_71])).
% 11.85/4.76  tff(c_25228, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_25225])).
% 11.85/4.76  tff(c_25232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_25228])).
% 11.85/4.76  tff(c_25233, plain, (![A_21]: (v1_funct_2(k1_xboole_0, A_21, k1_xboole_0) | k1_xboole_0=A_21)), inference(splitRight, [status(thm)], [c_71])).
% 11.85/4.76  tff(c_29431, plain, (![A_1671]: (v1_funct_2('#skF_1', A_1671, '#skF_1') | A_1671='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29241, c_29241, c_29241, c_25233])).
% 11.85/4.76  tff(c_29200, plain, (k2_funct_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_26851])).
% 11.85/4.76  tff(c_29205, plain, (~v1_funct_2(k1_xboole_0, '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29200, c_25125])).
% 11.85/4.76  tff(c_29242, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29241, c_29205])).
% 11.85/4.76  tff(c_29435, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_29431, c_29242])).
% 11.85/4.76  tff(c_29452, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29435, c_29242])).
% 11.85/4.76  tff(c_29244, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_29241, c_29200])).
% 11.85/4.76  tff(c_29288, plain, (![A_1665]: (k1_relat_1(k2_funct_1(A_1665))=k2_relat_1(A_1665) | ~v2_funct_1(A_1665) | ~v1_funct_1(A_1665) | ~v1_relat_1(A_1665))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.85/4.76  tff(c_29300, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29244, c_29288])).
% 11.85/4.76  tff(c_29304, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25159, c_68, c_62, c_29300])).
% 11.85/4.76  tff(c_29251, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29241, c_29241, c_12])).
% 11.85/4.76  tff(c_29322, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_29251, c_64])).
% 11.85/4.76  tff(c_29436, plain, (![A_1672, B_1673, C_1674]: (k2_relset_1(A_1672, B_1673, C_1674)=k2_relat_1(C_1674) | ~m1_subset_1(C_1674, k1_zfmisc_1(k2_zfmisc_1(A_1672, B_1673))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.85/4.76  tff(c_29578, plain, (![B_1682, C_1683]: (k2_relset_1('#skF_1', B_1682, C_1683)=k2_relat_1(C_1683) | ~m1_subset_1(C_1683, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_29251, c_29436])).
% 11.85/4.76  tff(c_29582, plain, (![B_1682]: (k2_relset_1('#skF_1', B_1682, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_29322, c_29578])).
% 11.85/4.76  tff(c_29598, plain, (![B_1685]: (k2_relset_1('#skF_1', B_1685, '#skF_3')=k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_29304, c_29582])).
% 11.85/4.76  tff(c_29453, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_29435, c_29435, c_60])).
% 11.85/4.76  tff(c_29602, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_29598, c_29453])).
% 11.85/4.76  tff(c_29395, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29304, c_48])).
% 11.85/4.76  tff(c_29401, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25159, c_68, c_29395])).
% 11.85/4.76  tff(c_29618, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29602, c_29401])).
% 11.85/4.76  tff(c_36, plain, (![C_23, A_21]: (k1_xboole_0=C_23 | ~v1_funct_2(C_23, A_21, k1_xboole_0) | k1_xboole_0=A_21 | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.85/4.76  tff(c_72, plain, (![C_23, A_21]: (k1_xboole_0=C_23 | ~v1_funct_2(C_23, A_21, k1_xboole_0) | k1_xboole_0=A_21 | ~m1_subset_1(C_23, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_36])).
% 11.85/4.76  tff(c_29560, plain, (![C_23, A_21]: (C_23='#skF_1' | ~v1_funct_2(C_23, A_21, '#skF_1') | A_21='#skF_1' | ~m1_subset_1(C_23, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_29241, c_29241, c_29241, c_29241, c_72])).
% 11.85/4.76  tff(c_29676, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_3')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_29618, c_29560])).
% 11.85/4.76  tff(c_29679, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_29322, c_29676])).
% 11.85/4.76  tff(c_29690, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_29679])).
% 11.85/4.76  tff(c_25173, plain, (![C_1450]: (v1_relat_1(C_1450) | ~m1_subset_1(C_1450, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_25142])).
% 11.85/4.76  tff(c_25179, plain, (![A_1451]: (v1_relat_1(A_1451) | ~r1_tarski(A_1451, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_25173])).
% 11.85/4.76  tff(c_25184, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_25179])).
% 11.85/4.76  tff(c_29248, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29241, c_25184])).
% 11.85/4.76  tff(c_29206, plain, (v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_29200, c_149])).
% 11.85/4.76  tff(c_29243, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29241, c_29206])).
% 11.85/4.76  tff(c_29223, plain, (![A_1664]: (k2_relat_1(k2_funct_1(A_1664))=k1_relat_1(A_1664) | ~v2_funct_1(A_1664) | ~v1_funct_1(A_1664) | ~v1_relat_1(A_1664))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.85/4.76  tff(c_29235, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29200, c_29223])).
% 11.85/4.76  tff(c_29239, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25159, c_68, c_62, c_29235])).
% 11.85/4.76  tff(c_29358, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_29241, c_29239])).
% 11.85/4.76  tff(c_29362, plain, (v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_29358, c_48])).
% 11.85/4.76  tff(c_29366, plain, (v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_29248, c_29243, c_29362])).
% 11.85/4.76  tff(c_29619, plain, (v1_funct_2('#skF_1', '#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_29602, c_29366])).
% 11.85/4.76  tff(c_29692, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29690, c_29619])).
% 11.85/4.76  tff(c_29697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29452, c_29692])).
% 11.85/4.76  tff(c_29698, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_29679])).
% 11.85/4.76  tff(c_29701, plain, (v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29698, c_29698, c_29618])).
% 11.85/4.76  tff(c_29715, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29602, c_29701])).
% 11.85/4.76  tff(c_29717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29452, c_29715])).
% 11.85/4.76  tff(c_29718, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_29199])).
% 11.85/4.76  tff(c_29719, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_29199])).
% 11.85/4.76  tff(c_29734, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_29718, c_29719])).
% 11.85/4.76  tff(c_29729, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_29718, c_29718, c_10])).
% 11.85/4.76  tff(c_29791, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_29729, c_64])).
% 11.85/4.76  tff(c_30039, plain, (![C_1706, A_1707]: (C_1706='#skF_2' | ~v1_funct_2(C_1706, A_1707, '#skF_2') | A_1707='#skF_2' | ~m1_subset_1(C_1706, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_29718, c_29718, c_29718, c_29718, c_72])).
% 11.85/4.76  tff(c_30043, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_66, c_30039])).
% 11.85/4.76  tff(c_30050, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_29791, c_30043])).
% 11.85/4.76  tff(c_30051, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_29734, c_30050])).
% 11.85/4.76  tff(c_25141, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_25129])).
% 11.85/4.76  tff(c_25168, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_25141, c_25160])).
% 11.85/4.76  tff(c_25185, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_25168])).
% 11.85/4.76  tff(c_29789, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_29729, c_25185])).
% 11.85/4.76  tff(c_30071, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30051, c_29789])).
% 11.85/4.76  tff(c_30085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_30071])).
% 11.85/4.76  tff(c_30086, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_25168])).
% 11.85/4.76  tff(c_30089, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30086, c_64])).
% 11.85/4.76  tff(c_30281, plain, (![A_1732, B_1733, C_1734]: (k2_relset_1(A_1732, B_1733, C_1734)=k2_relat_1(C_1734) | ~m1_subset_1(C_1734, k1_zfmisc_1(k2_zfmisc_1(A_1732, B_1733))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.85/4.76  tff(c_30407, plain, (![C_1752]: (k2_relset_1('#skF_1', '#skF_2', C_1752)=k2_relat_1(C_1752) | ~m1_subset_1(C_1752, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_30086, c_30281])).
% 11.85/4.76  tff(c_30410, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30089, c_30407])).
% 11.85/4.76  tff(c_30416, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_30410])).
% 11.85/4.76  tff(c_30225, plain, (![A_1722, B_1723, C_1724]: (k1_relset_1(A_1722, B_1723, C_1724)=k1_relat_1(C_1724) | ~m1_subset_1(C_1724, k1_zfmisc_1(k2_zfmisc_1(A_1722, B_1723))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.85/4.76  tff(c_30246, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_25126, c_30225])).
% 11.85/4.76  tff(c_31035, plain, (![B_1776, C_1777, A_1778]: (k1_xboole_0=B_1776 | v1_funct_2(C_1777, A_1778, B_1776) | k1_relset_1(A_1778, B_1776, C_1777)!=A_1778 | ~m1_subset_1(C_1777, k1_zfmisc_1(k2_zfmisc_1(A_1778, B_1776))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.85/4.76  tff(c_31058, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_25126, c_31035])).
% 11.85/4.76  tff(c_31078, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30246, c_31058])).
% 11.85/4.76  tff(c_31079, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_25125, c_31078])).
% 11.85/4.76  tff(c_31082, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_31079])).
% 11.85/4.76  tff(c_31085, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_31082])).
% 11.85/4.76  tff(c_31088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25159, c_68, c_62, c_30416, c_31085])).
% 11.85/4.76  tff(c_31089, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_31079])).
% 11.85/4.76  tff(c_30138, plain, (![B_1713, A_1714]: (k1_xboole_0=B_1713 | k1_xboole_0=A_1714 | k2_zfmisc_1(A_1714, B_1713)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.85/4.76  tff(c_30141, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_30086, c_30138])).
% 11.85/4.76  tff(c_30162, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_30141])).
% 11.85/4.76  tff(c_31117, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_31089, c_30162])).
% 11.85/4.76  tff(c_31122, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_31089, c_31089, c_12])).
% 11.85/4.76  tff(c_31231, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_31122, c_30086])).
% 11.85/4.76  tff(c_31233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31117, c_31231])).
% 11.85/4.76  tff(c_31235, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_30141])).
% 11.85/4.76  tff(c_33650, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31235, c_31235, c_12])).
% 11.85/4.76  tff(c_31234, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_30141])).
% 11.85/4.76  tff(c_33657, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_31235, c_31235, c_31234])).
% 11.85/4.76  tff(c_33658, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_33657])).
% 11.85/4.76  tff(c_31241, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31235, c_31235, c_12])).
% 11.85/4.76  tff(c_31390, plain, (![A_1794, B_1795, C_1796]: (k1_relset_1(A_1794, B_1795, C_1796)=k1_relat_1(C_1796) | ~m1_subset_1(C_1796, k1_zfmisc_1(k2_zfmisc_1(A_1794, B_1795))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.85/4.76  tff(c_31441, plain, (![B_1803, C_1804]: (k1_relset_1('#skF_3', B_1803, C_1804)=k1_relat_1(C_1804) | ~m1_subset_1(C_1804, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_31241, c_31390])).
% 11.85/4.76  tff(c_31450, plain, (![B_1803]: (k1_relset_1('#skF_3', B_1803, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_30089, c_31441])).
% 11.85/4.76  tff(c_38, plain, (![C_23, B_22]: (v1_funct_2(C_23, k1_xboole_0, B_22) | k1_relset_1(k1_xboole_0, B_22, C_23)!=k1_xboole_0 | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_22))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.85/4.76  tff(c_69, plain, (![C_23, B_22]: (v1_funct_2(C_23, k1_xboole_0, B_22) | k1_relset_1(k1_xboole_0, B_22, C_23)!=k1_xboole_0 | ~m1_subset_1(C_23, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_38])).
% 11.85/4.76  tff(c_31730, plain, (![C_1831, B_1832]: (v1_funct_2(C_1831, '#skF_3', B_1832) | k1_relset_1('#skF_3', B_1832, C_1831)!='#skF_3' | ~m1_subset_1(C_1831, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_31235, c_31235, c_31235, c_31235, c_69])).
% 11.85/4.76  tff(c_31740, plain, (![B_1832]: (v1_funct_2('#skF_3', '#skF_3', B_1832) | k1_relset_1('#skF_3', B_1832, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_30089, c_31730])).
% 11.85/4.76  tff(c_31750, plain, (![B_1832]: (v1_funct_2('#skF_3', '#skF_3', B_1832) | k1_relat_1('#skF_3')!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31450, c_31740])).
% 11.85/4.76  tff(c_31805, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(splitLeft, [status(thm)], [c_31750])).
% 11.85/4.76  tff(c_31248, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_31235, c_31235, c_31234])).
% 11.85/4.76  tff(c_31249, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_31248])).
% 11.85/4.76  tff(c_31252, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_31249, c_25126])).
% 11.85/4.76  tff(c_31314, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_31241, c_31252])).
% 11.85/4.76  tff(c_31452, plain, (![A_1805, B_1806, C_1807]: (k2_relset_1(A_1805, B_1806, C_1807)=k2_relat_1(C_1807) | ~m1_subset_1(C_1807, k1_zfmisc_1(k2_zfmisc_1(A_1805, B_1806))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.85/4.76  tff(c_31576, plain, (![B_1821, C_1822]: (k2_relset_1('#skF_3', B_1821, C_1822)=k2_relat_1(C_1822) | ~m1_subset_1(C_1822, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_31241, c_31452])).
% 11.85/4.76  tff(c_31703, plain, (![B_1830]: (k2_relset_1('#skF_3', B_1830, k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_31314, c_31576])).
% 11.85/4.76  tff(c_31715, plain, (![B_1830]: (m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1(B_1830)) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_1830))))), inference(superposition, [status(thm), theory('equality')], [c_31703, c_28])).
% 11.85/4.76  tff(c_31753, plain, (![B_1833]: (m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1(B_1833)))), inference(demodulation, [status(thm), theory('equality')], [c_31314, c_31241, c_31715])).
% 11.85/4.76  tff(c_31806, plain, (![B_1834]: (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), B_1834))), inference(resolution, [status(thm)], [c_31753, c_14])).
% 11.85/4.76  tff(c_31829, plain, (![B_1834]: (r1_tarski(k1_relat_1('#skF_3'), B_1834) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_31806])).
% 11.85/4.76  tff(c_31840, plain, (![B_1835]: (r1_tarski(k1_relat_1('#skF_3'), B_1835))), inference(demodulation, [status(thm), theory('equality')], [c_25159, c_68, c_62, c_31829])).
% 11.85/4.76  tff(c_31600, plain, (![B_1825]: (k2_relset_1('#skF_3', B_1825, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_30089, c_31576])).
% 11.85/4.76  tff(c_31612, plain, (![B_1825]: (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1(B_1825)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_1825))))), inference(superposition, [status(thm), theory('equality')], [c_31600, c_28])).
% 11.85/4.76  tff(c_31622, plain, (![B_1826]: (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1(B_1826)))), inference(demodulation, [status(thm), theory('equality')], [c_30089, c_31241, c_31612])).
% 11.85/4.76  tff(c_31665, plain, (![B_1827]: (r1_tarski(k2_relat_1('#skF_3'), B_1827))), inference(resolution, [status(thm)], [c_31622, c_14])).
% 11.85/4.76  tff(c_31688, plain, (![B_1827]: (k2_relat_1('#skF_3')=B_1827 | ~r1_tarski(B_1827, k2_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_31665, c_2])).
% 11.85/4.76  tff(c_31861, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_31840, c_31688])).
% 11.85/4.76  tff(c_31242, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31235, c_31235, c_10])).
% 11.85/4.76  tff(c_32404, plain, (![A_1865, B_1866, A_1867]: (k2_relset_1(A_1865, B_1866, A_1867)=k2_relat_1(A_1867) | ~r1_tarski(A_1867, k2_zfmisc_1(A_1865, B_1866)))), inference(resolution, [status(thm)], [c_16, c_31452])).
% 11.85/4.76  tff(c_32427, plain, (![A_1868, A_1869]: (k2_relset_1(A_1868, '#skF_3', A_1869)=k2_relat_1(A_1869) | ~r1_tarski(A_1869, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_31242, c_32404])).
% 11.85/4.76  tff(c_32435, plain, (![A_1868]: (k2_relset_1(A_1868, '#skF_3', '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_32427])).
% 11.85/4.76  tff(c_32444, plain, (![A_1870]: (k2_relset_1(A_1870, '#skF_3', '#skF_3')=k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_31861, c_32435])).
% 11.85/4.76  tff(c_31254, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_31249, c_31249, c_60])).
% 11.85/4.76  tff(c_32457, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_32444, c_31254])).
% 11.85/4.76  tff(c_32472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31805, c_32457])).
% 11.85/4.76  tff(c_32474, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_31750])).
% 11.85/4.76  tff(c_31790, plain, (![B_1833]: (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1(B_1833)) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_31753])).
% 11.85/4.76  tff(c_31804, plain, (![B_1833]: (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1(B_1833)))), inference(demodulation, [status(thm), theory('equality')], [c_25159, c_68, c_62, c_31790])).
% 11.85/4.76  tff(c_32532, plain, (![B_1874]: (m1_subset_1('#skF_3', k1_zfmisc_1(B_1874)))), inference(demodulation, [status(thm), theory('equality')], [c_32474, c_31804])).
% 11.85/4.76  tff(c_32585, plain, (![B_1874]: (r1_tarski('#skF_3', B_1874))), inference(resolution, [status(thm)], [c_32532, c_14])).
% 11.85/4.76  tff(c_31236, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_25167])).
% 11.85/4.76  tff(c_31304, plain, (~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_31241, c_31249, c_31236])).
% 11.85/4.76  tff(c_32602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32585, c_31304])).
% 11.85/4.76  tff(c_32603, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_31248])).
% 11.85/4.76  tff(c_32611, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32603, c_25159])).
% 11.85/4.76  tff(c_32619, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32603, c_68])).
% 11.85/4.76  tff(c_32618, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32603, c_62])).
% 11.85/4.76  tff(c_32608, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32603, c_32603, c_30089])).
% 11.85/4.76  tff(c_32630, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32603, c_32603, c_31241])).
% 11.85/4.76  tff(c_32755, plain, (![A_1887, B_1888, C_1889]: (k1_relset_1(A_1887, B_1888, C_1889)=k1_relat_1(C_1889) | ~m1_subset_1(C_1889, k1_zfmisc_1(k2_zfmisc_1(A_1887, B_1888))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.85/4.76  tff(c_32802, plain, (![B_1896, C_1897]: (k1_relset_1('#skF_1', B_1896, C_1897)=k1_relat_1(C_1897) | ~m1_subset_1(C_1897, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_32630, c_32755])).
% 11.85/4.76  tff(c_32811, plain, (![B_1896]: (k1_relset_1('#skF_1', B_1896, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_32608, c_32802])).
% 11.85/4.76  tff(c_32617, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32603, c_66])).
% 11.85/4.76  tff(c_32605, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32603, c_31235])).
% 11.85/4.76  tff(c_33065, plain, (![B_1924, C_1925]: (k1_relset_1('#skF_1', B_1924, C_1925)='#skF_1' | ~v1_funct_2(C_1925, '#skF_1', B_1924) | ~m1_subset_1(C_1925, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32605, c_32605, c_32605, c_32605, c_70])).
% 11.85/4.76  tff(c_33070, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_32617, c_33065])).
% 11.85/4.76  tff(c_33077, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32608, c_32811, c_33070])).
% 11.85/4.76  tff(c_32645, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32603, c_32603, c_31242])).
% 11.85/4.76  tff(c_32613, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32603, c_25126])).
% 11.85/4.76  tff(c_32700, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32645, c_32613])).
% 11.85/4.76  tff(c_32901, plain, (![A_1908, B_1909, C_1910]: (k2_relset_1(A_1908, B_1909, C_1910)=k2_relat_1(C_1910) | ~m1_subset_1(C_1910, k1_zfmisc_1(k2_zfmisc_1(A_1908, B_1909))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.85/4.76  tff(c_32952, plain, (![B_1917, C_1918]: (k2_relset_1('#skF_1', B_1917, C_1918)=k2_relat_1(C_1918) | ~m1_subset_1(C_1918, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_32630, c_32901])).
% 11.85/4.76  tff(c_32960, plain, (![B_1917]: (k2_relset_1('#skF_1', B_1917, k2_funct_1('#skF_1'))=k2_relat_1(k2_funct_1('#skF_1')))), inference(resolution, [status(thm)], [c_32700, c_32952])).
% 11.85/4.76  tff(c_33240, plain, (![A_1940, B_1941, C_1942]: (m1_subset_1(k2_relset_1(A_1940, B_1941, C_1942), k1_zfmisc_1(B_1941)) | ~m1_subset_1(C_1942, k1_zfmisc_1(k2_zfmisc_1(A_1940, B_1941))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.85/4.76  tff(c_33277, plain, (![B_1917]: (m1_subset_1(k2_relat_1(k2_funct_1('#skF_1')), k1_zfmisc_1(B_1917)) | ~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_1917))))), inference(superposition, [status(thm), theory('equality')], [c_32960, c_33240])).
% 11.85/4.76  tff(c_33498, plain, (![B_1949]: (m1_subset_1(k2_relat_1(k2_funct_1('#skF_1')), k1_zfmisc_1(B_1949)))), inference(demodulation, [status(thm), theory('equality')], [c_32700, c_32630, c_33277])).
% 11.85/4.76  tff(c_33535, plain, (![B_1949]: (m1_subset_1(k1_relat_1('#skF_1'), k1_zfmisc_1(B_1949)) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_33498])).
% 11.85/4.76  tff(c_33584, plain, (![B_1952]: (m1_subset_1('#skF_1', k1_zfmisc_1(B_1952)))), inference(demodulation, [status(thm), theory('equality')], [c_32611, c_32619, c_32618, c_33077, c_33535])).
% 11.85/4.76  tff(c_33638, plain, (![B_1952]: (r1_tarski('#skF_1', B_1952))), inference(resolution, [status(thm)], [c_33584, c_14])).
% 11.85/4.76  tff(c_32604, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_31248])).
% 11.85/4.76  tff(c_32624, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32603, c_32604])).
% 11.85/4.76  tff(c_32971, plain, (![B_1921]: (k2_relset_1('#skF_1', B_1921, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_32608, c_32952])).
% 11.85/4.76  tff(c_32616, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32603, c_60])).
% 11.85/4.76  tff(c_32978, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_32971, c_32616])).
% 11.85/4.76  tff(c_32917, plain, (![A_1911, C_1912]: (k2_relset_1(A_1911, '#skF_1', C_1912)=k2_relat_1(C_1912) | ~m1_subset_1(C_1912, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_32645, c_32901])).
% 11.85/4.76  tff(c_32926, plain, (![A_1911]: (k2_relset_1(A_1911, '#skF_1', '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_32608, c_32917])).
% 11.85/4.76  tff(c_32991, plain, (![A_1911]: (k2_relset_1(A_1911, '#skF_1', '#skF_1')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32978, c_32926])).
% 11.85/4.76  tff(c_33280, plain, (![A_1911]: (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_1911, '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_32991, c_33240])).
% 11.85/4.76  tff(c_33304, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32608, c_32645, c_33280])).
% 11.85/4.76  tff(c_33328, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_33304, c_14])).
% 11.85/4.76  tff(c_33341, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_33328, c_2])).
% 11.85/4.76  tff(c_33350, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_32624, c_33341])).
% 11.85/4.76  tff(c_33643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33638, c_33350])).
% 11.85/4.76  tff(c_33644, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_25167])).
% 11.85/4.76  tff(c_33707, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_33650, c_33658, c_33644])).
% 11.85/4.76  tff(c_33748, plain, (![A_1959]: (k1_relat_1(k2_funct_1(A_1959))=k2_relat_1(A_1959) | ~v2_funct_1(A_1959) | ~v1_funct_1(A_1959) | ~v1_relat_1(A_1959))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.85/4.76  tff(c_33760, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_33707, c_33748])).
% 11.85/4.76  tff(c_33764, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25159, c_68, c_62, c_33760])).
% 11.85/4.76  tff(c_33651, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31235, c_31235, c_10])).
% 11.85/4.76  tff(c_33792, plain, (![A_1961, B_1962, C_1963]: (k2_relset_1(A_1961, B_1962, C_1963)=k2_relat_1(C_1963) | ~m1_subset_1(C_1963, k1_zfmisc_1(k2_zfmisc_1(A_1961, B_1962))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.85/4.76  tff(c_33826, plain, (![A_1969, C_1970]: (k2_relset_1(A_1969, '#skF_3', C_1970)=k2_relat_1(C_1970) | ~m1_subset_1(C_1970, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_33651, c_33792])).
% 11.85/4.76  tff(c_33828, plain, (![A_1969]: (k2_relset_1(A_1969, '#skF_3', '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_30089, c_33826])).
% 11.85/4.76  tff(c_33835, plain, (![A_1971]: (k2_relset_1(A_1971, '#skF_3', '#skF_3')=k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_33764, c_33828])).
% 11.85/4.76  tff(c_33663, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_33658, c_33658, c_60])).
% 11.85/4.76  tff(c_33842, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_33835, c_33663])).
% 11.85/4.76  tff(c_33804, plain, (![B_1964, C_1965]: (k2_relset_1('#skF_3', B_1964, C_1965)=k2_relat_1(C_1965) | ~m1_subset_1(C_1965, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_33650, c_33792])).
% 11.85/4.76  tff(c_33806, plain, (![B_1964]: (k2_relset_1('#skF_3', B_1964, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_30089, c_33804])).
% 11.85/4.76  tff(c_33811, plain, (![B_1964]: (k2_relset_1('#skF_3', B_1964, '#skF_3')=k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_33764, c_33806])).
% 11.85/4.76  tff(c_33867, plain, (![B_1964]: (k2_relset_1('#skF_3', B_1964, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33842, c_33811])).
% 11.85/4.76  tff(c_34107, plain, (![A_2001, B_2002, C_2003]: (m1_subset_1(k2_relset_1(A_2001, B_2002, C_2003), k1_zfmisc_1(B_2002)) | ~m1_subset_1(C_2003, k1_zfmisc_1(k2_zfmisc_1(A_2001, B_2002))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.85/4.76  tff(c_34147, plain, (![B_1964]: (m1_subset_1('#skF_3', k1_zfmisc_1(B_1964)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_1964))))), inference(superposition, [status(thm), theory('equality')], [c_33867, c_34107])).
% 11.85/4.76  tff(c_34167, plain, (![B_2004]: (m1_subset_1('#skF_3', k1_zfmisc_1(B_2004)))), inference(demodulation, [status(thm), theory('equality')], [c_30089, c_33650, c_34147])).
% 11.85/4.76  tff(c_34215, plain, (![B_2004]: (r1_tarski('#skF_3', B_2004))), inference(resolution, [status(thm)], [c_34167, c_14])).
% 11.85/4.76  tff(c_33869, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_33842, c_33764])).
% 11.85/4.76  tff(c_33975, plain, (![B_1985, A_1986]: (v1_funct_2(B_1985, k1_relat_1(B_1985), A_1986) | ~r1_tarski(k2_relat_1(B_1985), A_1986) | ~v1_funct_1(B_1985) | ~v1_relat_1(B_1985))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.85/4.76  tff(c_33978, plain, (![A_1986]: (v1_funct_2('#skF_3', '#skF_3', A_1986) | ~r1_tarski(k2_relat_1('#skF_3'), A_1986) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_33842, c_33975])).
% 11.85/4.76  tff(c_33984, plain, (![A_1987]: (v1_funct_2('#skF_3', '#skF_3', A_1987) | ~r1_tarski('#skF_3', A_1987))), inference(demodulation, [status(thm), theory('equality')], [c_25159, c_68, c_33869, c_33978])).
% 11.85/4.76  tff(c_33662, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_33658, c_25125])).
% 11.85/4.76  tff(c_33730, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_33707, c_33662])).
% 11.85/4.76  tff(c_33988, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_33984, c_33730])).
% 11.85/4.76  tff(c_34220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34215, c_33988])).
% 11.85/4.76  tff(c_34221, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_33657])).
% 11.85/4.76  tff(c_34222, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_33657])).
% 11.85/4.76  tff(c_34242, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34221, c_34222])).
% 11.85/4.76  tff(c_34226, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34221, c_34221, c_30089])).
% 11.85/4.76  tff(c_34223, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34221, c_31235])).
% 11.85/4.76  tff(c_34287, plain, (![A_21]: (v1_funct_2('#skF_1', A_21, '#skF_1') | A_21='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34223, c_34223, c_34223, c_34223, c_34223, c_71])).
% 11.85/4.76  tff(c_34288, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_34287])).
% 11.85/4.76  tff(c_34295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34226, c_34288])).
% 11.85/4.76  tff(c_34375, plain, (![A_2011]: (v1_funct_2('#skF_1', A_2011, '#skF_1') | A_2011='#skF_1')), inference(splitRight, [status(thm)], [c_34287])).
% 11.85/4.76  tff(c_34248, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34221, c_34221, c_33651])).
% 11.85/4.76  tff(c_34308, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34221, c_34248, c_33644])).
% 11.85/4.76  tff(c_34232, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34221, c_25125])).
% 11.85/4.76  tff(c_34327, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34308, c_34232])).
% 11.85/4.76  tff(c_34378, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_34375, c_34327])).
% 11.85/4.76  tff(c_34382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34242, c_34378])).
% 11.85/4.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.85/4.76  
% 11.85/4.76  Inference rules
% 11.85/4.76  ----------------------
% 11.85/4.76  #Ref     : 0
% 11.85/4.76  #Sup     : 7278
% 11.85/4.76  #Fact    : 0
% 11.85/4.76  #Define  : 0
% 11.85/4.76  #Split   : 86
% 11.85/4.76  #Chain   : 0
% 11.85/4.76  #Close   : 0
% 11.85/4.76  
% 11.85/4.76  Ordering : KBO
% 11.85/4.76  
% 11.85/4.76  Simplification rules
% 11.85/4.76  ----------------------
% 11.85/4.76  #Subsume      : 976
% 11.85/4.76  #Demod        : 10196
% 11.85/4.76  #Tautology    : 3789
% 11.85/4.76  #SimpNegUnit  : 95
% 11.85/4.76  #BackRed      : 834
% 11.85/4.76  
% 11.85/4.76  #Partial instantiations: 0
% 11.85/4.76  #Strategies tried      : 1
% 11.85/4.76  
% 11.85/4.76  Timing (in seconds)
% 11.85/4.76  ----------------------
% 11.85/4.77  Preprocessing        : 0.33
% 11.85/4.77  Parsing              : 0.17
% 11.85/4.77  CNF conversion       : 0.02
% 11.85/4.77  Main loop            : 3.52
% 11.85/4.77  Inferencing          : 1.10
% 11.85/4.77  Reduction            : 1.36
% 11.85/4.77  Demodulation         : 1.00
% 11.85/4.77  BG Simplification    : 0.11
% 11.85/4.77  Subsumption          : 0.69
% 11.85/4.77  Abstraction          : 0.16
% 11.85/4.77  MUC search           : 0.00
% 11.85/4.77  Cooper               : 0.00
% 11.85/4.77  Total                : 4.05
% 11.85/4.77  Index Insertion      : 0.00
% 11.85/4.77  Index Deletion       : 0.00
% 11.85/4.77  Index Matching       : 0.00
% 11.85/4.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
