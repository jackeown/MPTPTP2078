%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:57 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 130 expanded)
%              Number of leaves         :   33 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :  104 ( 292 expanded)
%              Number of equality atoms :   34 (  97 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | r1_tarski(C,k8_relset_1(A,B,D,k7_relset_1(A,B,D,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_18,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_105,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_111,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_105])).

tff(c_118,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_111])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_57,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_160,plain,(
    ! [A_57,B_58,C_59] :
      ( k1_relset_1(A_57,B_58,C_59) = k1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_173,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_160])).

tff(c_392,plain,(
    ! [B_109,A_110,C_111] :
      ( k1_xboole_0 = B_109
      | k1_relset_1(A_110,B_109,C_111) = A_110
      | ~ v1_funct_2(C_111,A_110,B_109)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_399,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_392])).

tff(c_407,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_173,c_399])).

tff(c_408,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_407])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_502,plain,(
    ! [A_126,C_127,B_128] :
      ( r1_tarski(A_126,k10_relat_1(C_127,B_128))
      | ~ r1_tarski(k9_relat_1(C_127,A_126),B_128)
      | ~ r1_tarski(A_126,k1_relat_1(C_127))
      | ~ v1_funct_1(C_127)
      | ~ v1_relat_1(C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_520,plain,(
    ! [A_131,C_132] :
      ( r1_tarski(A_131,k10_relat_1(C_132,k9_relat_1(C_132,A_131)))
      | ~ r1_tarski(A_131,k1_relat_1(C_132))
      | ~ v1_funct_1(C_132)
      | ~ v1_relat_1(C_132) ) ),
    inference(resolution,[status(thm)],[c_6,c_502])).

tff(c_266,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k7_relset_1(A_82,B_83,C_84,D_85) = k9_relat_1(C_84,D_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_276,plain,(
    ! [D_85] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_85) = k9_relat_1('#skF_4',D_85) ),
    inference(resolution,[status(thm)],[c_46,c_266])).

tff(c_179,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( k8_relset_1(A_60,B_61,C_62,D_63) = k10_relat_1(C_62,D_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_189,plain,(
    ! [D_63] : k8_relset_1('#skF_1','#skF_2','#skF_4',D_63) = k10_relat_1('#skF_4',D_63) ),
    inference(resolution,[status(thm)],[c_46,c_179])).

tff(c_40,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_2','#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_198,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_40])).

tff(c_290,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_198])).

tff(c_527,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_520,c_290])).

tff(c_537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_50,c_44,c_408,c_527])).

tff(c_538,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_540,plain,(
    ! [A_3] : m1_subset_1('#skF_1',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_8])).

tff(c_555,plain,(
    ! [A_135,B_136] :
      ( r1_tarski(A_135,B_136)
      | ~ m1_subset_1(A_135,k1_zfmisc_1(B_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_563,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(resolution,[status(thm)],[c_540,c_555])).

tff(c_571,plain,(
    ! [B_140,A_141] :
      ( B_140 = A_141
      | ~ r1_tarski(B_140,A_141)
      | ~ r1_tarski(A_141,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_579,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_571])).

tff(c_588,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_579])).

tff(c_539,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_545,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_539])).

tff(c_564,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_4',k7_relset_1('#skF_1','#skF_1','#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_545,c_40])).

tff(c_589,plain,(
    ~ r1_tarski('#skF_1',k8_relset_1('#skF_1','#skF_1','#skF_4',k7_relset_1('#skF_1','#skF_1','#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_588,c_564])).

tff(c_593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_589])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:10:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.36  
% 2.67/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.37  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.67/1.37  
% 2.67/1.37  %Foreground sorts:
% 2.67/1.37  
% 2.67/1.37  
% 2.67/1.37  %Background operators:
% 2.67/1.37  
% 2.67/1.37  
% 2.67/1.37  %Foreground operators:
% 2.67/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.37  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.67/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.37  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.67/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.67/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.67/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.67/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.67/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.67/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.67/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.37  
% 2.67/1.38  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.67/1.38  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r1_tarski(C, k8_relset_1(A, B, D, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_2)).
% 2.67/1.38  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.67/1.38  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.67/1.38  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.67/1.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.67/1.38  tff(f_62, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 2.67/1.38  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.67/1.38  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.67/1.38  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.67/1.38  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.67/1.38  tff(c_18, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.67/1.38  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.67/1.38  tff(c_105, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.67/1.38  tff(c_111, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_105])).
% 2.67/1.38  tff(c_118, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_111])).
% 2.67/1.38  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.67/1.38  tff(c_44, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.67/1.38  tff(c_42, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.67/1.38  tff(c_57, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_42])).
% 2.67/1.38  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.67/1.38  tff(c_160, plain, (![A_57, B_58, C_59]: (k1_relset_1(A_57, B_58, C_59)=k1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.67/1.38  tff(c_173, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_160])).
% 2.67/1.38  tff(c_392, plain, (![B_109, A_110, C_111]: (k1_xboole_0=B_109 | k1_relset_1(A_110, B_109, C_111)=A_110 | ~v1_funct_2(C_111, A_110, B_109) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.67/1.38  tff(c_399, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_392])).
% 2.67/1.38  tff(c_407, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_173, c_399])).
% 2.67/1.38  tff(c_408, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_57, c_407])).
% 2.67/1.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.38  tff(c_502, plain, (![A_126, C_127, B_128]: (r1_tarski(A_126, k10_relat_1(C_127, B_128)) | ~r1_tarski(k9_relat_1(C_127, A_126), B_128) | ~r1_tarski(A_126, k1_relat_1(C_127)) | ~v1_funct_1(C_127) | ~v1_relat_1(C_127))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.67/1.38  tff(c_520, plain, (![A_131, C_132]: (r1_tarski(A_131, k10_relat_1(C_132, k9_relat_1(C_132, A_131))) | ~r1_tarski(A_131, k1_relat_1(C_132)) | ~v1_funct_1(C_132) | ~v1_relat_1(C_132))), inference(resolution, [status(thm)], [c_6, c_502])).
% 2.67/1.38  tff(c_266, plain, (![A_82, B_83, C_84, D_85]: (k7_relset_1(A_82, B_83, C_84, D_85)=k9_relat_1(C_84, D_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.67/1.38  tff(c_276, plain, (![D_85]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_85)=k9_relat_1('#skF_4', D_85))), inference(resolution, [status(thm)], [c_46, c_266])).
% 2.67/1.38  tff(c_179, plain, (![A_60, B_61, C_62, D_63]: (k8_relset_1(A_60, B_61, C_62, D_63)=k10_relat_1(C_62, D_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.67/1.38  tff(c_189, plain, (![D_63]: (k8_relset_1('#skF_1', '#skF_2', '#skF_4', D_63)=k10_relat_1('#skF_4', D_63))), inference(resolution, [status(thm)], [c_46, c_179])).
% 2.67/1.38  tff(c_40, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_2', '#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.67/1.38  tff(c_198, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_40])).
% 2.67/1.38  tff(c_290, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_198])).
% 2.67/1.38  tff(c_527, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_520, c_290])).
% 2.67/1.38  tff(c_537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_50, c_44, c_408, c_527])).
% 2.67/1.38  tff(c_538, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_42])).
% 2.67/1.38  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.38  tff(c_540, plain, (![A_3]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_538, c_8])).
% 2.67/1.38  tff(c_555, plain, (![A_135, B_136]: (r1_tarski(A_135, B_136) | ~m1_subset_1(A_135, k1_zfmisc_1(B_136)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.67/1.38  tff(c_563, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(resolution, [status(thm)], [c_540, c_555])).
% 2.67/1.38  tff(c_571, plain, (![B_140, A_141]: (B_140=A_141 | ~r1_tarski(B_140, A_141) | ~r1_tarski(A_141, B_140))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.38  tff(c_579, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_571])).
% 2.67/1.38  tff(c_588, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_563, c_579])).
% 2.67/1.38  tff(c_539, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_42])).
% 2.67/1.38  tff(c_545, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_538, c_539])).
% 2.67/1.38  tff(c_564, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_4', k7_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_545, c_545, c_40])).
% 2.67/1.38  tff(c_589, plain, (~r1_tarski('#skF_1', k8_relset_1('#skF_1', '#skF_1', '#skF_4', k7_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_588, c_564])).
% 2.67/1.38  tff(c_593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_563, c_589])).
% 2.67/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.38  
% 2.67/1.38  Inference rules
% 2.67/1.38  ----------------------
% 2.67/1.38  #Ref     : 0
% 2.67/1.38  #Sup     : 104
% 2.67/1.38  #Fact    : 0
% 2.67/1.38  #Define  : 0
% 2.67/1.38  #Split   : 6
% 2.67/1.38  #Chain   : 0
% 2.67/1.38  #Close   : 0
% 2.67/1.38  
% 2.67/1.38  Ordering : KBO
% 2.67/1.38  
% 2.67/1.38  Simplification rules
% 2.67/1.38  ----------------------
% 2.67/1.38  #Subsume      : 5
% 2.67/1.38  #Demod        : 51
% 2.67/1.38  #Tautology    : 53
% 2.67/1.38  #SimpNegUnit  : 9
% 2.67/1.38  #BackRed      : 9
% 2.67/1.38  
% 2.67/1.38  #Partial instantiations: 0
% 2.67/1.38  #Strategies tried      : 1
% 2.67/1.38  
% 2.67/1.38  Timing (in seconds)
% 2.67/1.38  ----------------------
% 2.67/1.38  Preprocessing        : 0.32
% 2.67/1.38  Parsing              : 0.17
% 2.67/1.38  CNF conversion       : 0.02
% 2.91/1.38  Main loop            : 0.30
% 2.91/1.38  Inferencing          : 0.11
% 2.91/1.38  Reduction            : 0.09
% 2.91/1.38  Demodulation         : 0.07
% 2.91/1.38  BG Simplification    : 0.02
% 2.91/1.38  Subsumption          : 0.05
% 2.91/1.38  Abstraction          : 0.01
% 2.91/1.39  MUC search           : 0.00
% 2.91/1.39  Cooper               : 0.00
% 2.91/1.39  Total                : 0.65
% 2.91/1.39  Index Insertion      : 0.00
% 2.91/1.39  Index Deletion       : 0.00
% 2.91/1.39  Index Matching       : 0.00
% 2.91/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
