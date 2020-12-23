%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:20 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  151 (4408 expanded)
%              Number of leaves         :   31 (1528 expanded)
%              Depth                    :   15
%              Number of atoms          :  257 (16538 expanded)
%              Number of equality atoms :  114 (6164 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_181,plain,(
    ! [A_53,B_54,D_55] :
      ( r2_relset_1(A_53,B_54,D_55,D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_194,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_181])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_108,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_125,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_108])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_46,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_206,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_225,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_206])).

tff(c_242,plain,(
    ! [B_66,A_67,C_68] :
      ( k1_xboole_0 = B_66
      | k1_relset_1(A_67,B_66,C_68) = A_67
      | ~ v1_funct_2(C_68,A_67,B_66)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_252,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_242])).

tff(c_265,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_225,c_252])).

tff(c_273,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_124,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_108])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_224,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_206])).

tff(c_249,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_242])).

tff(c_262,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_224,c_249])).

tff(c_267,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_485,plain,(
    ! [A_108,B_109] :
      ( r2_hidden('#skF_1'(A_108,B_109),k1_relat_1(A_108))
      | B_109 = A_108
      | k1_relat_1(B_109) != k1_relat_1(A_108)
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109)
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_494,plain,(
    ! [B_109] :
      ( r2_hidden('#skF_1'('#skF_4',B_109),'#skF_2')
      | B_109 = '#skF_4'
      | k1_relat_1(B_109) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_485])).

tff(c_505,plain,(
    ! [B_111] :
      ( r2_hidden('#skF_1'('#skF_4',B_111),'#skF_2')
      | B_111 = '#skF_4'
      | k1_relat_1(B_111) != '#skF_2'
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_54,c_267,c_494])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_515,plain,(
    ! [B_113] :
      ( m1_subset_1('#skF_1'('#skF_4',B_113),'#skF_2')
      | B_113 = '#skF_4'
      | k1_relat_1(B_113) != '#skF_2'
      | ~ v1_funct_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_505,c_10])).

tff(c_42,plain,(
    ! [E_31] :
      ( k1_funct_1('#skF_5',E_31) = k1_funct_1('#skF_4',E_31)
      | ~ m1_subset_1(E_31,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_648,plain,(
    ! [B_129] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_129)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_129))
      | B_129 = '#skF_4'
      | k1_relat_1(B_129) != '#skF_2'
      | ~ v1_funct_1(B_129)
      | ~ v1_relat_1(B_129) ) ),
    inference(resolution,[status(thm)],[c_515,c_42])).

tff(c_16,plain,(
    ! [B_12,A_8] :
      ( k1_funct_1(B_12,'#skF_1'(A_8,B_12)) != k1_funct_1(A_8,'#skF_1'(A_8,B_12))
      | B_12 = A_8
      | k1_relat_1(B_12) != k1_relat_1(A_8)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_655,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_16])).

tff(c_662,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_48,c_273,c_124,c_54,c_273,c_267,c_655])).

tff(c_40,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_675,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_40])).

tff(c_686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_675])).

tff(c_687,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_700,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_687,c_6])).

tff(c_741,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_50])).

tff(c_30,plain,(
    ! [C_26,A_24] :
      ( k1_xboole_0 = C_26
      | ~ v1_funct_2(C_26,A_24,k1_xboole_0)
      | k1_xboole_0 = A_24
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_58,plain,(
    ! [C_26,A_24] :
      ( k1_xboole_0 = C_26
      | ~ v1_funct_2(C_26,A_24,k1_xboole_0)
      | k1_xboole_0 = A_24
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_30])).

tff(c_708,plain,(
    ! [C_130,A_131] :
      ( C_130 = '#skF_3'
      | ~ v1_funct_2(C_130,A_131,'#skF_3')
      | A_131 = '#skF_3'
      | ~ m1_subset_1(C_130,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_687,c_687,c_687,c_58])).

tff(c_714,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_708])).

tff(c_738,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_714])).

tff(c_785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_738])).

tff(c_786,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_714])).

tff(c_833,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_786])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_24] :
      ( v1_funct_2(k1_xboole_0,A_24,k1_xboole_0)
      | k1_xboole_0 = A_24
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_24,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_57,plain,(
    ! [A_24] :
      ( v1_funct_2(k1_xboole_0,A_24,k1_xboole_0)
      | k1_xboole_0 = A_24
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_28])).

tff(c_160,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_163,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_160])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_163])).

tff(c_169,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_196,plain,(
    ! [A_56,D_57] :
      ( r2_relset_1(A_56,k1_xboole_0,D_57,D_57)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_181])).

tff(c_202,plain,(
    ! [A_56] : r2_relset_1(A_56,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_169,c_196])).

tff(c_692,plain,(
    ! [A_56] : r2_relset_1(A_56,'#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_687,c_687,c_202])).

tff(c_955,plain,(
    ! [A_56] : r2_relset_1(A_56,'#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_833,c_833,c_692])).

tff(c_791,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_44])).

tff(c_836,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_791])).

tff(c_713,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_2' = '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_708])).

tff(c_973,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_833,c_833,c_833,c_713])).

tff(c_974,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_973])).

tff(c_688,plain,(
    k1_relat_1('#skF_5') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_979,plain,(
    k1_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_688])).

tff(c_845,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_687])).

tff(c_219,plain,(
    ! [A_2,C_63] :
      ( k1_relset_1(A_2,k1_xboole_0,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_206])).

tff(c_1130,plain,(
    ! [A_176,C_177] :
      ( k1_relset_1(A_176,'#skF_4',C_177) = k1_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_845,c_219])).

tff(c_1138,plain,(
    ! [A_176] : k1_relset_1(A_176,'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_836,c_1130])).

tff(c_850,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_46])).

tff(c_978,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_850])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    ! [B_25,C_26] :
      ( k1_relset_1(k1_xboole_0,B_25,C_26) = k1_xboole_0
      | ~ v1_funct_2(C_26,k1_xboole_0,B_25)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_56,plain,(
    ! [B_25,C_26] :
      ( k1_relset_1(k1_xboole_0,B_25,C_26) = k1_xboole_0
      | ~ v1_funct_2(C_26,k1_xboole_0,B_25)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_36])).

tff(c_831,plain,(
    ! [B_25,C_26] :
      ( k1_relset_1('#skF_3',B_25,C_26) = '#skF_3'
      | ~ v1_funct_2(C_26,'#skF_3',B_25)
      | ~ m1_subset_1(C_26,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_687,c_687,c_687,c_56])).

tff(c_1326,plain,(
    ! [B_207,C_208] :
      ( k1_relset_1('#skF_4',B_207,C_208) = '#skF_4'
      | ~ v1_funct_2(C_208,'#skF_4',B_207)
      | ~ m1_subset_1(C_208,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_833,c_833,c_833,c_831])).

tff(c_1335,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_978,c_1326])).

tff(c_1346,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_1138,c_1335])).

tff(c_1348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_979,c_1346])).

tff(c_1349,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_973])).

tff(c_849,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_40])).

tff(c_1352,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1349,c_849])).

tff(c_1363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_955,c_1352])).

tff(c_1364,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_786])).

tff(c_1366,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1364,c_688])).

tff(c_1373,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1364,c_46])).

tff(c_1412,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1373,c_831])).

tff(c_1417,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_791,c_1412])).

tff(c_1368,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1364,c_225])).

tff(c_1528,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1417,c_1368])).

tff(c_1529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1366,c_1528])).

tff(c_1530,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_1543,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1530,c_1530,c_6])).

tff(c_1589,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1543,c_50])).

tff(c_1580,plain,(
    ! [C_225,A_226] :
      ( C_225 = '#skF_3'
      | ~ v1_funct_2(C_225,A_226,'#skF_3')
      | A_226 = '#skF_3'
      | ~ m1_subset_1(C_225,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1530,c_1530,c_1530,c_1530,c_58])).

tff(c_1586,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_1580])).

tff(c_1689,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_1586])).

tff(c_1690,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1689])).

tff(c_1531,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_1691,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_1531])).

tff(c_1699,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_52])).

tff(c_1717,plain,(
    ! [B_235,C_236] :
      ( k1_relset_1('#skF_3',B_235,C_236) = '#skF_3'
      | ~ v1_funct_2(C_236,'#skF_3',B_235)
      | ~ m1_subset_1(C_236,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1530,c_1530,c_1530,c_1530,c_56])).

tff(c_1719,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1699,c_1717])).

tff(c_1727,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_1719])).

tff(c_1693,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_224])).

tff(c_1745,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1727,c_1693])).

tff(c_1746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1691,c_1745])).

tff(c_1747,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1689])).

tff(c_1535,plain,(
    ! [A_56] : r2_relset_1(A_56,'#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1530,c_1530,c_1530,c_202])).

tff(c_1752,plain,(
    ! [A_56] : r2_relset_1(A_56,'#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1747,c_1747,c_1747,c_1535])).

tff(c_1748,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1689])).

tff(c_1779,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1747,c_1748])).

tff(c_1590,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1543,c_44])).

tff(c_1755,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1747,c_1590])).

tff(c_1585,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_2' = '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_1580])).

tff(c_1910,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1755,c_1747,c_1747,c_1747,c_1585])).

tff(c_1911,plain,(
    '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1779,c_1910])).

tff(c_1770,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1747,c_40])).

tff(c_1913,plain,(
    ~ r2_relset_1('#skF_2','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1911,c_1770])).

tff(c_1923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1752,c_1913])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:29:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.63  
% 3.82/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.63  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.82/1.63  
% 3.82/1.63  %Foreground sorts:
% 3.82/1.63  
% 3.82/1.63  
% 3.82/1.63  %Background operators:
% 3.82/1.63  
% 3.82/1.63  
% 3.82/1.63  %Foreground operators:
% 3.82/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.82/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.82/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.82/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.82/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.82/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.82/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.82/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.82/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.82/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.82/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.82/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.82/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.82/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.82/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.82/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.82/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.82/1.63  
% 3.82/1.66  tff(f_114, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 3.82/1.66  tff(f_75, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.82/1.66  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.82/1.66  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.82/1.66  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.82/1.66  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 3.82/1.66  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.82/1.66  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.82/1.66  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.82/1.66  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.82/1.66  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.82/1.66  tff(c_181, plain, (![A_53, B_54, D_55]: (r2_relset_1(A_53, B_54, D_55, D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.82/1.66  tff(c_194, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_181])).
% 3.82/1.66  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.82/1.66  tff(c_108, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.82/1.66  tff(c_125, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_108])).
% 3.82/1.66  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.82/1.66  tff(c_46, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.82/1.66  tff(c_206, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.82/1.66  tff(c_225, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_206])).
% 3.82/1.66  tff(c_242, plain, (![B_66, A_67, C_68]: (k1_xboole_0=B_66 | k1_relset_1(A_67, B_66, C_68)=A_67 | ~v1_funct_2(C_68, A_67, B_66) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.82/1.66  tff(c_252, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_242])).
% 3.82/1.66  tff(c_265, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_225, c_252])).
% 3.82/1.66  tff(c_273, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_265])).
% 3.82/1.66  tff(c_124, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_108])).
% 3.82/1.66  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.82/1.66  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.82/1.66  tff(c_224, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_206])).
% 3.82/1.66  tff(c_249, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_242])).
% 3.82/1.66  tff(c_262, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_224, c_249])).
% 3.82/1.66  tff(c_267, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_262])).
% 3.82/1.66  tff(c_485, plain, (![A_108, B_109]: (r2_hidden('#skF_1'(A_108, B_109), k1_relat_1(A_108)) | B_109=A_108 | k1_relat_1(B_109)!=k1_relat_1(A_108) | ~v1_funct_1(B_109) | ~v1_relat_1(B_109) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.82/1.66  tff(c_494, plain, (![B_109]: (r2_hidden('#skF_1'('#skF_4', B_109), '#skF_2') | B_109='#skF_4' | k1_relat_1(B_109)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_109) | ~v1_relat_1(B_109) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_267, c_485])).
% 3.82/1.66  tff(c_505, plain, (![B_111]: (r2_hidden('#skF_1'('#skF_4', B_111), '#skF_2') | B_111='#skF_4' | k1_relat_1(B_111)!='#skF_2' | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_54, c_267, c_494])).
% 3.82/1.66  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1(A_4, B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.82/1.66  tff(c_515, plain, (![B_113]: (m1_subset_1('#skF_1'('#skF_4', B_113), '#skF_2') | B_113='#skF_4' | k1_relat_1(B_113)!='#skF_2' | ~v1_funct_1(B_113) | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_505, c_10])).
% 3.82/1.66  tff(c_42, plain, (![E_31]: (k1_funct_1('#skF_5', E_31)=k1_funct_1('#skF_4', E_31) | ~m1_subset_1(E_31, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.82/1.66  tff(c_648, plain, (![B_129]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_129))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_129)) | B_129='#skF_4' | k1_relat_1(B_129)!='#skF_2' | ~v1_funct_1(B_129) | ~v1_relat_1(B_129))), inference(resolution, [status(thm)], [c_515, c_42])).
% 3.82/1.66  tff(c_16, plain, (![B_12, A_8]: (k1_funct_1(B_12, '#skF_1'(A_8, B_12))!=k1_funct_1(A_8, '#skF_1'(A_8, B_12)) | B_12=A_8 | k1_relat_1(B_12)!=k1_relat_1(A_8) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.82/1.66  tff(c_655, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_648, c_16])).
% 3.82/1.66  tff(c_662, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_48, c_273, c_124, c_54, c_273, c_267, c_655])).
% 3.82/1.66  tff(c_40, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.82/1.66  tff(c_675, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_662, c_40])).
% 3.82/1.66  tff(c_686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_675])).
% 3.82/1.66  tff(c_687, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_265])).
% 3.82/1.66  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.82/1.66  tff(c_700, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_687, c_687, c_6])).
% 3.82/1.66  tff(c_741, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_700, c_50])).
% 3.82/1.66  tff(c_30, plain, (![C_26, A_24]: (k1_xboole_0=C_26 | ~v1_funct_2(C_26, A_24, k1_xboole_0) | k1_xboole_0=A_24 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.82/1.66  tff(c_58, plain, (![C_26, A_24]: (k1_xboole_0=C_26 | ~v1_funct_2(C_26, A_24, k1_xboole_0) | k1_xboole_0=A_24 | ~m1_subset_1(C_26, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_30])).
% 3.82/1.66  tff(c_708, plain, (![C_130, A_131]: (C_130='#skF_3' | ~v1_funct_2(C_130, A_131, '#skF_3') | A_131='#skF_3' | ~m1_subset_1(C_130, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_687, c_687, c_687, c_687, c_58])).
% 3.82/1.66  tff(c_714, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_708])).
% 3.82/1.66  tff(c_738, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_714])).
% 3.82/1.66  tff(c_785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_741, c_738])).
% 3.82/1.66  tff(c_786, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_714])).
% 3.82/1.66  tff(c_833, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_786])).
% 3.82/1.66  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.82/1.66  tff(c_14, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.82/1.66  tff(c_28, plain, (![A_24]: (v1_funct_2(k1_xboole_0, A_24, k1_xboole_0) | k1_xboole_0=A_24 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_24, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.82/1.66  tff(c_57, plain, (![A_24]: (v1_funct_2(k1_xboole_0, A_24, k1_xboole_0) | k1_xboole_0=A_24 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_28])).
% 3.82/1.66  tff(c_160, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_57])).
% 3.82/1.66  tff(c_163, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_160])).
% 3.82/1.66  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_163])).
% 3.82/1.66  tff(c_169, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_57])).
% 3.82/1.66  tff(c_196, plain, (![A_56, D_57]: (r2_relset_1(A_56, k1_xboole_0, D_57, D_57) | ~m1_subset_1(D_57, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_181])).
% 3.82/1.66  tff(c_202, plain, (![A_56]: (r2_relset_1(A_56, k1_xboole_0, k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_169, c_196])).
% 3.82/1.66  tff(c_692, plain, (![A_56]: (r2_relset_1(A_56, '#skF_3', '#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_687, c_687, c_687, c_202])).
% 3.82/1.66  tff(c_955, plain, (![A_56]: (r2_relset_1(A_56, '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_833, c_833, c_833, c_692])).
% 3.82/1.66  tff(c_791, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_700, c_44])).
% 3.82/1.66  tff(c_836, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_833, c_791])).
% 3.82/1.66  tff(c_713, plain, ('#skF_5'='#skF_3' | '#skF_2'='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_708])).
% 3.82/1.66  tff(c_973, plain, ('#skF_5'='#skF_4' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_836, c_833, c_833, c_833, c_713])).
% 3.82/1.66  tff(c_974, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_973])).
% 3.82/1.66  tff(c_688, plain, (k1_relat_1('#skF_5')!='#skF_2'), inference(splitRight, [status(thm)], [c_265])).
% 3.82/1.66  tff(c_979, plain, (k1_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_974, c_688])).
% 3.82/1.66  tff(c_845, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_833, c_687])).
% 3.82/1.66  tff(c_219, plain, (![A_2, C_63]: (k1_relset_1(A_2, k1_xboole_0, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_206])).
% 3.82/1.66  tff(c_1130, plain, (![A_176, C_177]: (k1_relset_1(A_176, '#skF_4', C_177)=k1_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_845, c_845, c_219])).
% 3.82/1.66  tff(c_1138, plain, (![A_176]: (k1_relset_1(A_176, '#skF_4', '#skF_5')=k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_836, c_1130])).
% 3.82/1.66  tff(c_850, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_833, c_46])).
% 3.82/1.66  tff(c_978, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_974, c_850])).
% 3.82/1.66  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.82/1.66  tff(c_36, plain, (![B_25, C_26]: (k1_relset_1(k1_xboole_0, B_25, C_26)=k1_xboole_0 | ~v1_funct_2(C_26, k1_xboole_0, B_25) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_25))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.82/1.66  tff(c_56, plain, (![B_25, C_26]: (k1_relset_1(k1_xboole_0, B_25, C_26)=k1_xboole_0 | ~v1_funct_2(C_26, k1_xboole_0, B_25) | ~m1_subset_1(C_26, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_36])).
% 3.82/1.66  tff(c_831, plain, (![B_25, C_26]: (k1_relset_1('#skF_3', B_25, C_26)='#skF_3' | ~v1_funct_2(C_26, '#skF_3', B_25) | ~m1_subset_1(C_26, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_687, c_687, c_687, c_687, c_56])).
% 3.82/1.66  tff(c_1326, plain, (![B_207, C_208]: (k1_relset_1('#skF_4', B_207, C_208)='#skF_4' | ~v1_funct_2(C_208, '#skF_4', B_207) | ~m1_subset_1(C_208, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_833, c_833, c_833, c_833, c_831])).
% 3.82/1.66  tff(c_1335, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_978, c_1326])).
% 3.82/1.66  tff(c_1346, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_836, c_1138, c_1335])).
% 3.82/1.66  tff(c_1348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_979, c_1346])).
% 3.82/1.66  tff(c_1349, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_973])).
% 3.82/1.66  tff(c_849, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_833, c_40])).
% 3.82/1.66  tff(c_1352, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1349, c_849])).
% 3.82/1.66  tff(c_1363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_955, c_1352])).
% 3.82/1.66  tff(c_1364, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_786])).
% 3.82/1.66  tff(c_1366, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1364, c_688])).
% 3.82/1.66  tff(c_1373, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1364, c_46])).
% 3.82/1.66  tff(c_1412, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_1373, c_831])).
% 3.82/1.66  tff(c_1417, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_791, c_1412])).
% 3.82/1.66  tff(c_1368, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1364, c_225])).
% 3.82/1.66  tff(c_1528, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1417, c_1368])).
% 3.82/1.66  tff(c_1529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1366, c_1528])).
% 3.82/1.66  tff(c_1530, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_262])).
% 3.82/1.66  tff(c_1543, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1530, c_1530, c_6])).
% 3.82/1.66  tff(c_1589, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1543, c_50])).
% 3.82/1.66  tff(c_1580, plain, (![C_225, A_226]: (C_225='#skF_3' | ~v1_funct_2(C_225, A_226, '#skF_3') | A_226='#skF_3' | ~m1_subset_1(C_225, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1530, c_1530, c_1530, c_1530, c_58])).
% 3.82/1.66  tff(c_1586, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_1580])).
% 3.82/1.66  tff(c_1689, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1589, c_1586])).
% 3.82/1.66  tff(c_1690, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_1689])).
% 3.82/1.66  tff(c_1531, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitRight, [status(thm)], [c_262])).
% 3.82/1.66  tff(c_1691, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_1531])).
% 3.82/1.66  tff(c_1699, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_52])).
% 3.82/1.66  tff(c_1717, plain, (![B_235, C_236]: (k1_relset_1('#skF_3', B_235, C_236)='#skF_3' | ~v1_funct_2(C_236, '#skF_3', B_235) | ~m1_subset_1(C_236, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1530, c_1530, c_1530, c_1530, c_56])).
% 3.82/1.66  tff(c_1719, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_1699, c_1717])).
% 3.82/1.66  tff(c_1727, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1589, c_1719])).
% 3.82/1.66  tff(c_1693, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_224])).
% 3.82/1.66  tff(c_1745, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1727, c_1693])).
% 3.82/1.66  tff(c_1746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1691, c_1745])).
% 3.82/1.66  tff(c_1747, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_1689])).
% 3.82/1.66  tff(c_1535, plain, (![A_56]: (r2_relset_1(A_56, '#skF_3', '#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1530, c_1530, c_1530, c_202])).
% 3.82/1.66  tff(c_1752, plain, (![A_56]: (r2_relset_1(A_56, '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1747, c_1747, c_1747, c_1535])).
% 3.82/1.66  tff(c_1748, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_1689])).
% 3.82/1.66  tff(c_1779, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1747, c_1748])).
% 3.82/1.66  tff(c_1590, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1543, c_44])).
% 3.82/1.66  tff(c_1755, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1747, c_1590])).
% 3.82/1.66  tff(c_1585, plain, ('#skF_5'='#skF_3' | '#skF_2'='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_1580])).
% 3.82/1.66  tff(c_1910, plain, ('#skF_5'='#skF_4' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1755, c_1747, c_1747, c_1747, c_1585])).
% 3.82/1.66  tff(c_1911, plain, ('#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1779, c_1910])).
% 3.82/1.66  tff(c_1770, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1747, c_40])).
% 3.82/1.66  tff(c_1913, plain, (~r2_relset_1('#skF_2', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1911, c_1770])).
% 3.82/1.66  tff(c_1923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1752, c_1913])).
% 3.82/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.66  
% 3.82/1.66  Inference rules
% 3.82/1.66  ----------------------
% 3.82/1.66  #Ref     : 2
% 3.82/1.66  #Sup     : 375
% 3.82/1.66  #Fact    : 0
% 3.82/1.66  #Define  : 0
% 3.82/1.66  #Split   : 8
% 3.82/1.66  #Chain   : 0
% 3.82/1.66  #Close   : 0
% 3.82/1.66  
% 3.82/1.66  Ordering : KBO
% 3.82/1.66  
% 3.82/1.66  Simplification rules
% 3.82/1.66  ----------------------
% 3.82/1.66  #Subsume      : 55
% 3.82/1.66  #Demod        : 519
% 3.82/1.66  #Tautology    : 270
% 3.82/1.66  #SimpNegUnit  : 11
% 3.82/1.66  #BackRed      : 139
% 3.82/1.66  
% 3.82/1.66  #Partial instantiations: 0
% 3.82/1.66  #Strategies tried      : 1
% 3.82/1.66  
% 3.82/1.66  Timing (in seconds)
% 3.82/1.66  ----------------------
% 3.82/1.66  Preprocessing        : 0.33
% 3.82/1.66  Parsing              : 0.17
% 3.82/1.66  CNF conversion       : 0.02
% 3.82/1.66  Main loop            : 0.55
% 3.82/1.66  Inferencing          : 0.19
% 3.82/1.66  Reduction            : 0.19
% 3.82/1.66  Demodulation         : 0.13
% 3.82/1.66  BG Simplification    : 0.03
% 3.82/1.66  Subsumption          : 0.09
% 3.82/1.66  Abstraction          : 0.02
% 3.82/1.66  MUC search           : 0.00
% 3.82/1.66  Cooper               : 0.00
% 3.82/1.66  Total                : 0.93
% 3.82/1.66  Index Insertion      : 0.00
% 3.82/1.66  Index Deletion       : 0.00
% 3.82/1.66  Index Matching       : 0.00
% 3.82/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
