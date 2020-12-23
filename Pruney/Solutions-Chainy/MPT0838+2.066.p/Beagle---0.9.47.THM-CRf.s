%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:18 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 207 expanded)
%              Number of leaves         :   35 (  82 expanded)
%              Depth                    :    8
%              Number of atoms          :  120 ( 419 expanded)
%              Number of equality atoms :   50 ( 133 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_107,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_18,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_151,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_157,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_151])).

tff(c_161,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_157])).

tff(c_20,plain,(
    ! [A_16] :
      ( k2_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_169,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_161,c_20])).

tff(c_177,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_244,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_253,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_244])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_266,plain,(
    ! [A_85,C_86,B_87] :
      ( m1_subset_1(A_85,C_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(C_86))
      | ~ r2_hidden(A_85,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_275,plain,(
    ! [A_91,B_92,A_93] :
      ( m1_subset_1(A_91,B_92)
      | ~ r2_hidden(A_91,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(resolution,[status(thm)],[c_6,c_266])).

tff(c_302,plain,(
    ! [A_98,B_99] :
      ( m1_subset_1('#skF_1'(A_98),B_99)
      | ~ r1_tarski(A_98,B_99)
      | k1_xboole_0 = A_98 ) ),
    inference(resolution,[status(thm)],[c_2,c_275])).

tff(c_279,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_288,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_279])).

tff(c_66,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_45,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_71,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_66])).

tff(c_185,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_289,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_185])).

tff(c_305,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_302,c_289])).

tff(c_331,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_305])).

tff(c_340,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_331])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_253,c_340])).

tff(c_345,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_498,plain,(
    ! [A_139,B_140,C_141] :
      ( k2_relset_1(A_139,B_140,C_141) = k2_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_509,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_498])).

tff(c_513,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_509])).

tff(c_515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_513])).

tff(c_516,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_26,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_72,plain,(
    ! [A_46] :
      ( k2_relat_1(A_46) != k1_xboole_0
      | k1_xboole_0 = A_46
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_78,plain,(
    ! [A_13] :
      ( k2_relat_1(k6_relat_1(A_13)) != k1_xboole_0
      | k6_relat_1(A_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_72])).

tff(c_83,plain,(
    ! [A_47] :
      ( k1_xboole_0 != A_47
      | k6_relat_1(A_47) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_78])).

tff(c_24,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_89,plain,(
    ! [A_47] :
      ( k1_relat_1(k1_xboole_0) = A_47
      | k1_xboole_0 != A_47 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_24])).

tff(c_578,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_516,c_89])).

tff(c_22,plain,(
    ! [A_16] :
      ( k1_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_168,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_161,c_22])).

tff(c_170,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_518,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_170])).

tff(c_581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_518])).

tff(c_582,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_38,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_591,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_38])).

tff(c_583,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_597,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_583])).

tff(c_925,plain,(
    ! [A_197,B_198,C_199] :
      ( k1_relset_1(A_197,B_198,C_199) = k1_relat_1(C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_936,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_925])).

tff(c_940,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_936])).

tff(c_942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_591,c_940])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:52:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.43  
% 3.05/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.43  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.05/1.43  
% 3.05/1.43  %Foreground sorts:
% 3.05/1.43  
% 3.05/1.43  
% 3.05/1.43  %Background operators:
% 3.05/1.43  
% 3.05/1.43  
% 3.05/1.43  %Foreground operators:
% 3.05/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.05/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.05/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.05/1.43  tff('#skF_2', type, '#skF_2': $i).
% 3.05/1.43  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.05/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.05/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.05/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.05/1.43  tff('#skF_4', type, '#skF_4': $i).
% 3.05/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.05/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.05/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.05/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.05/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.43  
% 3.05/1.45  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.05/1.45  tff(f_107, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 3.05/1.45  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.05/1.45  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.05/1.45  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.05/1.45  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.05/1.45  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.05/1.45  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.05/1.45  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.05/1.45  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.05/1.45  tff(f_72, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.05/1.45  tff(f_58, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.05/1.45  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.05/1.45  tff(c_18, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.05/1.45  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.05/1.45  tff(c_151, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.05/1.45  tff(c_157, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_151])).
% 3.05/1.45  tff(c_161, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_157])).
% 3.05/1.45  tff(c_20, plain, (![A_16]: (k2_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.05/1.45  tff(c_169, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_161, c_20])).
% 3.05/1.45  tff(c_177, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_169])).
% 3.05/1.45  tff(c_244, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.05/1.45  tff(c_253, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_244])).
% 3.05/1.45  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.05/1.45  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.05/1.45  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.05/1.45  tff(c_266, plain, (![A_85, C_86, B_87]: (m1_subset_1(A_85, C_86) | ~m1_subset_1(B_87, k1_zfmisc_1(C_86)) | ~r2_hidden(A_85, B_87))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.45  tff(c_275, plain, (![A_91, B_92, A_93]: (m1_subset_1(A_91, B_92) | ~r2_hidden(A_91, A_93) | ~r1_tarski(A_93, B_92))), inference(resolution, [status(thm)], [c_6, c_266])).
% 3.05/1.45  tff(c_302, plain, (![A_98, B_99]: (m1_subset_1('#skF_1'(A_98), B_99) | ~r1_tarski(A_98, B_99) | k1_xboole_0=A_98)), inference(resolution, [status(thm)], [c_2, c_275])).
% 3.05/1.45  tff(c_279, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.05/1.45  tff(c_288, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_279])).
% 3.05/1.45  tff(c_66, plain, (![D_45]: (~r2_hidden(D_45, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_45, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.05/1.45  tff(c_71, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_66])).
% 3.05/1.45  tff(c_185, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_71])).
% 3.05/1.45  tff(c_289, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_288, c_185])).
% 3.05/1.45  tff(c_305, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_302, c_289])).
% 3.05/1.45  tff(c_331, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_177, c_305])).
% 3.05/1.45  tff(c_340, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_331])).
% 3.05/1.45  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_253, c_340])).
% 3.05/1.45  tff(c_345, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_71])).
% 3.05/1.45  tff(c_498, plain, (![A_139, B_140, C_141]: (k2_relset_1(A_139, B_140, C_141)=k2_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.05/1.45  tff(c_509, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_498])).
% 3.05/1.45  tff(c_513, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_345, c_509])).
% 3.05/1.45  tff(c_515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_177, c_513])).
% 3.05/1.45  tff(c_516, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_169])).
% 3.05/1.45  tff(c_26, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.05/1.45  tff(c_16, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.05/1.45  tff(c_72, plain, (![A_46]: (k2_relat_1(A_46)!=k1_xboole_0 | k1_xboole_0=A_46 | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.05/1.45  tff(c_78, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))!=k1_xboole_0 | k6_relat_1(A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_72])).
% 3.05/1.45  tff(c_83, plain, (![A_47]: (k1_xboole_0!=A_47 | k6_relat_1(A_47)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_78])).
% 3.05/1.45  tff(c_24, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.05/1.45  tff(c_89, plain, (![A_47]: (k1_relat_1(k1_xboole_0)=A_47 | k1_xboole_0!=A_47)), inference(superposition, [status(thm), theory('equality')], [c_83, c_24])).
% 3.05/1.45  tff(c_578, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_516, c_516, c_89])).
% 3.05/1.45  tff(c_22, plain, (![A_16]: (k1_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.05/1.45  tff(c_168, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_161, c_22])).
% 3.05/1.45  tff(c_170, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_168])).
% 3.05/1.45  tff(c_518, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_516, c_170])).
% 3.05/1.45  tff(c_581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_578, c_518])).
% 3.05/1.45  tff(c_582, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_168])).
% 3.05/1.45  tff(c_38, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.05/1.45  tff(c_591, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_582, c_38])).
% 3.05/1.45  tff(c_583, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_168])).
% 3.05/1.45  tff(c_597, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_582, c_583])).
% 3.05/1.45  tff(c_925, plain, (![A_197, B_198, C_199]: (k1_relset_1(A_197, B_198, C_199)=k1_relat_1(C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.05/1.45  tff(c_936, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_925])).
% 3.05/1.45  tff(c_940, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_597, c_936])).
% 3.05/1.45  tff(c_942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_591, c_940])).
% 3.05/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.45  
% 3.05/1.45  Inference rules
% 3.05/1.45  ----------------------
% 3.05/1.45  #Ref     : 4
% 3.05/1.45  #Sup     : 171
% 3.05/1.45  #Fact    : 0
% 3.05/1.45  #Define  : 0
% 3.05/1.45  #Split   : 8
% 3.05/1.45  #Chain   : 0
% 3.05/1.45  #Close   : 0
% 3.05/1.45  
% 3.05/1.45  Ordering : KBO
% 3.05/1.45  
% 3.05/1.45  Simplification rules
% 3.05/1.45  ----------------------
% 3.05/1.45  #Subsume      : 17
% 3.05/1.45  #Demod        : 99
% 3.05/1.45  #Tautology    : 66
% 3.05/1.45  #SimpNegUnit  : 7
% 3.05/1.45  #BackRed      : 23
% 3.05/1.45  
% 3.05/1.45  #Partial instantiations: 0
% 3.05/1.45  #Strategies tried      : 1
% 3.05/1.45  
% 3.05/1.45  Timing (in seconds)
% 3.05/1.45  ----------------------
% 3.05/1.45  Preprocessing        : 0.32
% 3.05/1.45  Parsing              : 0.17
% 3.05/1.45  CNF conversion       : 0.02
% 3.05/1.45  Main loop            : 0.37
% 3.05/1.45  Inferencing          : 0.14
% 3.05/1.45  Reduction            : 0.11
% 3.05/1.45  Demodulation         : 0.07
% 3.05/1.45  BG Simplification    : 0.02
% 3.05/1.45  Subsumption          : 0.05
% 3.05/1.45  Abstraction          : 0.02
% 3.05/1.45  MUC search           : 0.00
% 3.05/1.45  Cooper               : 0.00
% 3.05/1.45  Total                : 0.73
% 3.05/1.45  Index Insertion      : 0.00
% 3.05/1.45  Index Deletion       : 0.00
% 3.05/1.45  Index Matching       : 0.00
% 3.05/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
