%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:25 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 162 expanded)
%              Number of leaves         :   35 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  137 ( 412 expanded)
%              Number of equality atoms :   40 ( 122 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ! [C] :
            ~ ( r2_hidden(C,A)
              & ! [D] :
                  ~ ( r2_hidden(D,k1_relat_1(B))
                    & C = k1_funct_1(B,D) ) )
       => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_funct_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_129,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_133,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_129])).

tff(c_42,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_134,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_42])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_90,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_93,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_90])).

tff(c_96,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_93])).

tff(c_107,plain,(
    ! [C_49,B_50,A_51] :
      ( v5_relat_1(C_49,B_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_111,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_107])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_1'(A_11,B_12),A_11)
      | r1_tarski(A_11,k2_relat_1(B_12))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_52,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_5'(D_33),'#skF_2')
      | ~ r2_hidden(D_33,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_139,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_143,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_139])).

tff(c_174,plain,(
    ! [B_77,A_78,C_79] :
      ( k1_xboole_0 = B_77
      | k1_relset_1(A_78,B_77,C_79) = A_78
      | ~ v1_funct_2(C_79,A_78,B_77)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_177,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_174])).

tff(c_180,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_143,c_177])).

tff(c_181,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_50,plain,(
    ! [D_33] :
      ( k1_funct_1('#skF_4','#skF_5'(D_33)) = D_33
      | ~ r2_hidden(D_33,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_197,plain,(
    ! [B_83,D_84,A_85] :
      ( k1_funct_1(B_83,D_84) != '#skF_1'(A_85,B_83)
      | ~ r2_hidden(D_84,k1_relat_1(B_83))
      | r1_tarski(A_85,k2_relat_1(B_83))
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_199,plain,(
    ! [D_33,A_85] :
      ( D_33 != '#skF_1'(A_85,'#skF_4')
      | ~ r2_hidden('#skF_5'(D_33),k1_relat_1('#skF_4'))
      | r1_tarski(A_85,k2_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(D_33,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_197])).

tff(c_201,plain,(
    ! [D_33,A_85] :
      ( D_33 != '#skF_1'(A_85,'#skF_4')
      | ~ r2_hidden('#skF_5'(D_33),'#skF_2')
      | r1_tarski(A_85,k2_relat_1('#skF_4'))
      | ~ r2_hidden(D_33,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_48,c_181,c_199])).

tff(c_207,plain,(
    ! [A_88] :
      ( ~ r2_hidden('#skF_5'('#skF_1'(A_88,'#skF_4')),'#skF_2')
      | r1_tarski(A_88,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_88,'#skF_4'),'#skF_3') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_201])).

tff(c_212,plain,(
    ! [A_89] :
      ( r1_tarski(A_89,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_89,'#skF_4'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_207])).

tff(c_216,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_212])).

tff(c_219,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_48,c_216])).

tff(c_97,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(k2_relat_1(B_46),A_47)
      | ~ v5_relat_1(B_46,A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [B_46,A_47] :
      ( k2_relat_1(B_46) = A_47
      | ~ r1_tarski(A_47,k2_relat_1(B_46))
      | ~ v5_relat_1(B_46,A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_222,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_219,c_105])).

tff(c_227,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_111,c_222])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_227])).

tff(c_230,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    ! [B_40,A_41] :
      ( B_40 = A_41
      | ~ r1_tarski(B_40,A_41)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_58])).

tff(c_260,plain,(
    ! [A_94] :
      ( A_94 = '#skF_3'
      | ~ r1_tarski(A_94,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_230,c_67])).

tff(c_283,plain,(
    ! [B_98] :
      ( k2_relat_1(B_98) = '#skF_3'
      | ~ v5_relat_1(B_98,'#skF_3')
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_14,c_260])).

tff(c_286,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_111,c_283])).

tff(c_289,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_286])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_289])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:47:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.44  
% 2.47/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.47/1.44  
% 2.47/1.44  %Foreground sorts:
% 2.47/1.44  
% 2.47/1.44  
% 2.47/1.44  %Background operators:
% 2.47/1.44  
% 2.47/1.44  
% 2.47/1.44  %Foreground operators:
% 2.47/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.47/1.44  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.47/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.47/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.47/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.47/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.47/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.47/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.47/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.47/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.47/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.47/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.44  
% 2.75/1.46  tff(f_115, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 2.75/1.46  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.75/1.46  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.75/1.46  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.75/1.46  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.75/1.46  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.75/1.46  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, k1_relat_1(B)) & (C = k1_funct_1(B, D)))))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_funct_1)).
% 2.75/1.46  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.75/1.46  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.75/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.75/1.46  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.75/1.46  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.75/1.46  tff(c_129, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.75/1.46  tff(c_133, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_129])).
% 2.75/1.46  tff(c_42, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.75/1.46  tff(c_134, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_42])).
% 2.75/1.46  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.75/1.46  tff(c_90, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.46  tff(c_93, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_90])).
% 2.75/1.46  tff(c_96, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_93])).
% 2.75/1.46  tff(c_107, plain, (![C_49, B_50, A_51]: (v5_relat_1(C_49, B_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.75/1.46  tff(c_111, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_107])).
% 2.75/1.46  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.75/1.46  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.75/1.46  tff(c_20, plain, (![A_11, B_12]: (r2_hidden('#skF_1'(A_11, B_12), A_11) | r1_tarski(A_11, k2_relat_1(B_12)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.75/1.46  tff(c_52, plain, (![D_33]: (r2_hidden('#skF_5'(D_33), '#skF_2') | ~r2_hidden(D_33, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.75/1.46  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.75/1.46  tff(c_139, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.75/1.46  tff(c_143, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_139])).
% 2.75/1.46  tff(c_174, plain, (![B_77, A_78, C_79]: (k1_xboole_0=B_77 | k1_relset_1(A_78, B_77, C_79)=A_78 | ~v1_funct_2(C_79, A_78, B_77) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.75/1.46  tff(c_177, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_174])).
% 2.75/1.46  tff(c_180, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_143, c_177])).
% 2.75/1.46  tff(c_181, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_180])).
% 2.75/1.46  tff(c_50, plain, (![D_33]: (k1_funct_1('#skF_4', '#skF_5'(D_33))=D_33 | ~r2_hidden(D_33, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.75/1.46  tff(c_197, plain, (![B_83, D_84, A_85]: (k1_funct_1(B_83, D_84)!='#skF_1'(A_85, B_83) | ~r2_hidden(D_84, k1_relat_1(B_83)) | r1_tarski(A_85, k2_relat_1(B_83)) | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.75/1.46  tff(c_199, plain, (![D_33, A_85]: (D_33!='#skF_1'(A_85, '#skF_4') | ~r2_hidden('#skF_5'(D_33), k1_relat_1('#skF_4')) | r1_tarski(A_85, k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden(D_33, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_197])).
% 2.75/1.46  tff(c_201, plain, (![D_33, A_85]: (D_33!='#skF_1'(A_85, '#skF_4') | ~r2_hidden('#skF_5'(D_33), '#skF_2') | r1_tarski(A_85, k2_relat_1('#skF_4')) | ~r2_hidden(D_33, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_48, c_181, c_199])).
% 2.75/1.46  tff(c_207, plain, (![A_88]: (~r2_hidden('#skF_5'('#skF_1'(A_88, '#skF_4')), '#skF_2') | r1_tarski(A_88, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_88, '#skF_4'), '#skF_3'))), inference(reflexivity, [status(thm), theory('equality')], [c_201])).
% 2.75/1.46  tff(c_212, plain, (![A_89]: (r1_tarski(A_89, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_89, '#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_207])).
% 2.75/1.46  tff(c_216, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_212])).
% 2.75/1.46  tff(c_219, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_48, c_216])).
% 2.75/1.46  tff(c_97, plain, (![B_46, A_47]: (r1_tarski(k2_relat_1(B_46), A_47) | ~v5_relat_1(B_46, A_47) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.75/1.46  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.46  tff(c_105, plain, (![B_46, A_47]: (k2_relat_1(B_46)=A_47 | ~r1_tarski(A_47, k2_relat_1(B_46)) | ~v5_relat_1(B_46, A_47) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_97, c_2])).
% 2.75/1.46  tff(c_222, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_219, c_105])).
% 2.75/1.46  tff(c_227, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_111, c_222])).
% 2.75/1.46  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_227])).
% 2.75/1.46  tff(c_230, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_180])).
% 2.75/1.46  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.46  tff(c_58, plain, (![B_40, A_41]: (B_40=A_41 | ~r1_tarski(B_40, A_41) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.46  tff(c_67, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_58])).
% 2.75/1.46  tff(c_260, plain, (![A_94]: (A_94='#skF_3' | ~r1_tarski(A_94, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_230, c_67])).
% 2.75/1.46  tff(c_283, plain, (![B_98]: (k2_relat_1(B_98)='#skF_3' | ~v5_relat_1(B_98, '#skF_3') | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_14, c_260])).
% 2.75/1.46  tff(c_286, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_111, c_283])).
% 2.75/1.46  tff(c_289, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_286])).
% 2.75/1.46  tff(c_291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_289])).
% 2.75/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.46  
% 2.75/1.46  Inference rules
% 2.75/1.46  ----------------------
% 2.75/1.46  #Ref     : 1
% 2.75/1.46  #Sup     : 44
% 2.75/1.46  #Fact    : 0
% 2.75/1.46  #Define  : 0
% 2.75/1.46  #Split   : 1
% 2.75/1.46  #Chain   : 0
% 2.75/1.46  #Close   : 0
% 2.75/1.46  
% 2.75/1.46  Ordering : KBO
% 2.75/1.46  
% 2.75/1.46  Simplification rules
% 2.75/1.46  ----------------------
% 2.75/1.46  #Subsume      : 4
% 2.75/1.46  #Demod        : 45
% 2.75/1.46  #Tautology    : 22
% 2.75/1.46  #SimpNegUnit  : 2
% 2.75/1.46  #BackRed      : 10
% 2.75/1.46  
% 2.75/1.46  #Partial instantiations: 0
% 2.75/1.46  #Strategies tried      : 1
% 2.75/1.46  
% 2.75/1.46  Timing (in seconds)
% 2.75/1.46  ----------------------
% 2.75/1.47  Preprocessing        : 0.32
% 2.75/1.47  Parsing              : 0.16
% 2.75/1.47  CNF conversion       : 0.02
% 2.75/1.47  Main loop            : 0.31
% 2.75/1.47  Inferencing          : 0.11
% 2.75/1.47  Reduction            : 0.09
% 2.75/1.47  Demodulation         : 0.07
% 2.75/1.47  BG Simplification    : 0.02
% 2.75/1.47  Subsumption          : 0.05
% 2.75/1.47  Abstraction          : 0.01
% 2.75/1.47  MUC search           : 0.00
% 2.75/1.47  Cooper               : 0.00
% 2.75/1.47  Total                : 0.66
% 2.75/1.47  Index Insertion      : 0.00
% 2.75/1.47  Index Deletion       : 0.00
% 2.75/1.47  Index Matching       : 0.00
% 2.75/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
