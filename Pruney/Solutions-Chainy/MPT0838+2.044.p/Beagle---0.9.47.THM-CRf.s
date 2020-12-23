%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:15 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 241 expanded)
%              Number of leaves         :   36 (  93 expanded)
%              Depth                    :    8
%              Number of atoms          :  121 ( 486 expanded)
%              Number of equality atoms :   37 ( 124 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_26,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_148,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_155,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_148])).

tff(c_159,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_155])).

tff(c_28,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_167,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_159,c_28])).

tff(c_169,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_185,plain,(
    ! [C_71,B_72,A_73] :
      ( v5_relat_1(C_71,B_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_199,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_185])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_200,plain,(
    ! [C_74,B_75,A_76] :
      ( r2_hidden(C_74,B_75)
      | ~ r2_hidden(C_74,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_239,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_1'(A_85),B_86)
      | ~ r1_tarski(A_85,B_86)
      | v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_4,c_200])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_334,plain,(
    ! [A_99,B_100] :
      ( m1_subset_1('#skF_1'(A_99),B_100)
      | ~ r1_tarski(A_99,B_100)
      | v1_xboole_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_239,c_16])).

tff(c_280,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_294,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_280])).

tff(c_137,plain,(
    ! [D_61] :
      ( ~ r2_hidden(D_61,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_61,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_147,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_137])).

tff(c_183,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_295,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_183])).

tff(c_354,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_334,c_295])).

tff(c_359,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_354])).

tff(c_362,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_359])).

tff(c_369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_199,c_362])).

tff(c_370,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_354])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_379,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_370,c_14])).

tff(c_387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_379])).

tff(c_388,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_397,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_388,c_14])).

tff(c_648,plain,(
    ! [A_145,B_146,C_147] :
      ( k2_relset_1(A_145,B_146,C_147) = k2_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_663,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_648])).

tff(c_668,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_663])).

tff(c_670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_668])).

tff(c_671,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_57,plain,(
    ! [A_48] :
      ( v1_xboole_0(k1_relat_1(A_48))
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_62,plain,(
    ! [A_49] :
      ( k1_relat_1(A_49) = k1_xboole_0
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_57,c_14])).

tff(c_70,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_62])).

tff(c_677,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_671,c_70])).

tff(c_30,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_166,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_159,c_30])).

tff(c_168,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_673,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_168])).

tff(c_701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_673])).

tff(c_702,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_42,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_709,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_42])).

tff(c_707,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_702,c_70])).

tff(c_1040,plain,(
    ! [A_191,B_192,C_193] :
      ( k1_relset_1(A_191,B_192,C_193) = k1_relat_1(C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1055,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1040])).

tff(c_1060,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_707,c_1055])).

tff(c_1062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_709,c_1060])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.52  
% 3.33/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.53  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.33/1.53  
% 3.33/1.53  %Foreground sorts:
% 3.33/1.53  
% 3.33/1.53  
% 3.33/1.53  %Background operators:
% 3.33/1.53  
% 3.33/1.53  
% 3.33/1.53  %Foreground operators:
% 3.33/1.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.33/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.33/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.33/1.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.33/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.33/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.33/1.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.33/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.33/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.53  
% 3.35/1.54  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.35/1.54  tff(f_109, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.35/1.54  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.35/1.54  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.35/1.54  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.35/1.54  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.35/1.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.35/1.54  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.35/1.54  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.35/1.54  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.35/1.54  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.35/1.54  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.35/1.54  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.35/1.54  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.35/1.54  tff(c_26, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.35/1.54  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.35/1.54  tff(c_148, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.35/1.54  tff(c_155, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_148])).
% 3.35/1.54  tff(c_159, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_155])).
% 3.35/1.54  tff(c_28, plain, (![A_21]: (k2_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.54  tff(c_167, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_159, c_28])).
% 3.35/1.54  tff(c_169, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_167])).
% 3.35/1.54  tff(c_185, plain, (![C_71, B_72, A_73]: (v5_relat_1(C_71, B_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.35/1.54  tff(c_199, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_185])).
% 3.35/1.54  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.35/1.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.35/1.54  tff(c_200, plain, (![C_74, B_75, A_76]: (r2_hidden(C_74, B_75) | ~r2_hidden(C_74, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.35/1.54  tff(c_239, plain, (![A_85, B_86]: (r2_hidden('#skF_1'(A_85), B_86) | ~r1_tarski(A_85, B_86) | v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_4, c_200])).
% 3.35/1.54  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.35/1.54  tff(c_334, plain, (![A_99, B_100]: (m1_subset_1('#skF_1'(A_99), B_100) | ~r1_tarski(A_99, B_100) | v1_xboole_0(A_99))), inference(resolution, [status(thm)], [c_239, c_16])).
% 3.35/1.54  tff(c_280, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.35/1.54  tff(c_294, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_280])).
% 3.35/1.54  tff(c_137, plain, (![D_61]: (~r2_hidden(D_61, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_61, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.35/1.54  tff(c_147, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_137])).
% 3.35/1.54  tff(c_183, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_147])).
% 3.35/1.54  tff(c_295, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_183])).
% 3.35/1.54  tff(c_354, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | v1_xboole_0(k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_334, c_295])).
% 3.35/1.54  tff(c_359, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_354])).
% 3.35/1.54  tff(c_362, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_359])).
% 3.35/1.54  tff(c_369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_199, c_362])).
% 3.35/1.54  tff(c_370, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_354])).
% 3.35/1.54  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.35/1.54  tff(c_379, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_370, c_14])).
% 3.35/1.54  tff(c_387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_379])).
% 3.35/1.54  tff(c_388, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_147])).
% 3.35/1.54  tff(c_397, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_388, c_14])).
% 3.35/1.54  tff(c_648, plain, (![A_145, B_146, C_147]: (k2_relset_1(A_145, B_146, C_147)=k2_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.35/1.54  tff(c_663, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_648])).
% 3.35/1.54  tff(c_668, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_397, c_663])).
% 3.35/1.54  tff(c_670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_668])).
% 3.35/1.54  tff(c_671, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_167])).
% 3.35/1.54  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.35/1.54  tff(c_57, plain, (![A_48]: (v1_xboole_0(k1_relat_1(A_48)) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.35/1.54  tff(c_62, plain, (![A_49]: (k1_relat_1(A_49)=k1_xboole_0 | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_57, c_14])).
% 3.35/1.54  tff(c_70, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_62])).
% 3.35/1.54  tff(c_677, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_671, c_671, c_70])).
% 3.35/1.54  tff(c_30, plain, (![A_21]: (k1_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.54  tff(c_166, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_159, c_30])).
% 3.35/1.54  tff(c_168, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_166])).
% 3.35/1.54  tff(c_673, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_671, c_168])).
% 3.35/1.54  tff(c_701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_677, c_673])).
% 3.35/1.54  tff(c_702, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_166])).
% 3.35/1.54  tff(c_42, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.35/1.54  tff(c_709, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_702, c_42])).
% 3.35/1.54  tff(c_707, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_702, c_702, c_70])).
% 3.35/1.54  tff(c_1040, plain, (![A_191, B_192, C_193]: (k1_relset_1(A_191, B_192, C_193)=k1_relat_1(C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.35/1.54  tff(c_1055, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_1040])).
% 3.35/1.54  tff(c_1060, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_707, c_1055])).
% 3.35/1.54  tff(c_1062, plain, $false, inference(negUnitSimplification, [status(thm)], [c_709, c_1060])).
% 3.35/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.54  
% 3.35/1.54  Inference rules
% 3.35/1.54  ----------------------
% 3.35/1.54  #Ref     : 0
% 3.35/1.54  #Sup     : 204
% 3.35/1.54  #Fact    : 0
% 3.35/1.54  #Define  : 0
% 3.35/1.54  #Split   : 6
% 3.35/1.54  #Chain   : 0
% 3.35/1.54  #Close   : 0
% 3.35/1.54  
% 3.35/1.54  Ordering : KBO
% 3.35/1.54  
% 3.35/1.54  Simplification rules
% 3.35/1.54  ----------------------
% 3.35/1.54  #Subsume      : 12
% 3.35/1.54  #Demod        : 98
% 3.35/1.54  #Tautology    : 69
% 3.35/1.54  #SimpNegUnit  : 4
% 3.35/1.54  #BackRed      : 30
% 3.35/1.54  
% 3.35/1.54  #Partial instantiations: 0
% 3.35/1.54  #Strategies tried      : 1
% 3.35/1.54  
% 3.35/1.54  Timing (in seconds)
% 3.35/1.54  ----------------------
% 3.35/1.55  Preprocessing        : 0.33
% 3.35/1.55  Parsing              : 0.17
% 3.35/1.55  CNF conversion       : 0.02
% 3.35/1.55  Main loop            : 0.43
% 3.35/1.55  Inferencing          : 0.17
% 3.35/1.55  Reduction            : 0.12
% 3.35/1.55  Demodulation         : 0.08
% 3.35/1.55  BG Simplification    : 0.02
% 3.35/1.55  Subsumption          : 0.08
% 3.35/1.55  Abstraction          : 0.02
% 3.35/1.55  MUC search           : 0.00
% 3.35/1.55  Cooper               : 0.00
% 3.35/1.55  Total                : 0.80
% 3.35/1.55  Index Insertion      : 0.00
% 3.35/1.55  Index Deletion       : 0.00
% 3.35/1.55  Index Matching       : 0.00
% 3.35/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
