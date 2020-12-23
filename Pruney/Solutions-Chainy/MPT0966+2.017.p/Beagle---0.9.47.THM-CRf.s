%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:10 EST 2020

% Result     : Theorem 9.94s
% Output     : CNFRefutation 10.15s
% Verified   : 
% Statistics : Number of formulae       :  269 (2427 expanded)
%              Number of leaves         :   44 ( 790 expanded)
%              Depth                    :   14
%              Number of atoms          :  482 (6788 expanded)
%              Number of equality atoms :  189 (2332 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_156,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_136,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_38,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_19715,plain,(
    ! [B_1292,A_1293] :
      ( v1_relat_1(B_1292)
      | ~ m1_subset_1(B_1292,k1_zfmisc_1(A_1293))
      | ~ v1_relat_1(A_1293) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_19721,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_19715])).

tff(c_19725,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_19721])).

tff(c_19931,plain,(
    ! [C_1325,A_1326,B_1327] :
      ( v4_relat_1(C_1325,A_1326)
      | ~ m1_subset_1(C_1325,k1_zfmisc_1(k2_zfmisc_1(A_1326,B_1327))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_19946,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_19931])).

tff(c_34,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20083,plain,(
    ! [A_1346,B_1347,C_1348] :
      ( k2_relset_1(A_1346,B_1347,C_1348) = k2_relat_1(C_1348)
      | ~ m1_subset_1(C_1348,k1_zfmisc_1(k2_zfmisc_1(A_1346,B_1347))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_20098,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_20083])).

tff(c_72,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_20100,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20098,c_72])).

tff(c_20379,plain,(
    ! [C_1371,A_1372,B_1373] :
      ( m1_subset_1(C_1371,k1_zfmisc_1(k2_zfmisc_1(A_1372,B_1373)))
      | ~ r1_tarski(k2_relat_1(C_1371),B_1373)
      | ~ r1_tarski(k1_relat_1(C_1371),A_1372)
      | ~ v1_relat_1(C_1371) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_12,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_70,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_101,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_76,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_610,plain,(
    ! [A_114,B_115,C_116] :
      ( k1_relset_1(A_114,B_115,C_116) = k1_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_625,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_610])).

tff(c_1057,plain,(
    ! [B_159,A_160,C_161] :
      ( k1_xboole_0 = B_159
      | k1_relset_1(A_160,B_159,C_161) = A_160
      | ~ v1_funct_2(C_161,A_160,B_159)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1070,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1057])).

tff(c_1081,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_625,c_1070])).

tff(c_1082,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_1081])).

tff(c_259,plain,(
    ! [B_63,A_64] :
      ( v1_relat_1(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_265,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_259])).

tff(c_269,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_265])).

tff(c_671,plain,(
    ! [A_121,B_122,C_123] :
      ( k2_relset_1(A_121,B_122,C_123) = k2_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_686,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_671])).

tff(c_688,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_72])).

tff(c_920,plain,(
    ! [C_143,A_144,B_145] :
      ( m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ r1_tarski(k2_relat_1(C_143),B_145)
      | ~ r1_tarski(k1_relat_1(C_143),A_144)
      | ~ v1_relat_1(C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4685,plain,(
    ! [C_338,A_339,B_340] :
      ( r1_tarski(C_338,k2_zfmisc_1(A_339,B_340))
      | ~ r1_tarski(k2_relat_1(C_338),B_340)
      | ~ r1_tarski(k1_relat_1(C_338),A_339)
      | ~ v1_relat_1(C_338) ) ),
    inference(resolution,[status(thm)],[c_920,c_24])).

tff(c_4693,plain,(
    ! [A_339] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_339,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_339)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_688,c_4685])).

tff(c_4720,plain,(
    ! [A_341] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_341,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_341) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_1082,c_4693])).

tff(c_26,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_624,plain,(
    ! [A_114,B_115,A_10] :
      ( k1_relset_1(A_114,B_115,A_10) = k1_relat_1(A_10)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_114,B_115)) ) ),
    inference(resolution,[status(thm)],[c_26,c_610])).

tff(c_4723,plain,(
    ! [A_341] :
      ( k1_relset_1(A_341,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_341) ) ),
    inference(resolution,[status(thm)],[c_4720,c_624])).

tff(c_4785,plain,(
    ! [A_343] :
      ( k1_relset_1(A_343,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_343) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1082,c_4723])).

tff(c_4790,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12,c_4785])).

tff(c_292,plain,(
    ! [A_67,B_68] :
      ( v1_relat_1(A_67)
      | ~ v1_relat_1(B_68)
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_26,c_259])).

tff(c_312,plain,
    ( v1_relat_1(k2_relset_1('#skF_2','#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_292])).

tff(c_334,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_4711,plain,(
    ! [A_339] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_339,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_339) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_1082,c_4693])).

tff(c_1177,plain,(
    ! [B_168,C_169,A_170] :
      ( k1_xboole_0 = B_168
      | v1_funct_2(C_169,A_170,B_168)
      | k1_relset_1(A_170,B_168,C_169) != A_170
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_170,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_5516,plain,(
    ! [B_371,A_372,A_373] :
      ( k1_xboole_0 = B_371
      | v1_funct_2(A_372,A_373,B_371)
      | k1_relset_1(A_373,B_371,A_372) != A_373
      | ~ r1_tarski(A_372,k2_zfmisc_1(A_373,B_371)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1177])).

tff(c_5555,plain,(
    ! [A_339] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_339,'#skF_4')
      | k1_relset_1(A_339,'#skF_4','#skF_5') != A_339
      | ~ r1_tarski('#skF_2',A_339) ) ),
    inference(resolution,[status(thm)],[c_4711,c_5516])).

tff(c_5709,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5555])).

tff(c_22,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_117,plain,(
    ! [A_46,B_47] : v1_relat_1(k2_zfmisc_1(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_119,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_117])).

tff(c_5797,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5709,c_119])).

tff(c_5805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_5797])).

tff(c_6054,plain,(
    ! [A_389] :
      ( v1_funct_2('#skF_5',A_389,'#skF_4')
      | k1_relset_1(A_389,'#skF_4','#skF_5') != A_389
      | ~ r1_tarski('#skF_2',A_389) ) ),
    inference(splitRight,[status(thm)],[c_5555])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_80,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_68])).

tff(c_227,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_6060,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_6054,c_227])).

tff(c_6065,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4790,c_6060])).

tff(c_6067,plain,(
    v1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_44,plain,(
    ! [A_25] :
      ( k1_relat_1(A_25) != k1_xboole_0
      | k1_xboole_0 = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6074,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6067,c_44])).

tff(c_6084,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6074])).

tff(c_6410,plain,(
    ! [A_436,B_437,C_438] :
      ( k1_relset_1(A_436,B_437,C_438) = k1_relat_1(C_438)
      | ~ m1_subset_1(C_438,k1_zfmisc_1(k2_zfmisc_1(A_436,B_437))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6425,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_6410])).

tff(c_6857,plain,(
    ! [B_482,A_483,C_484] :
      ( k1_xboole_0 = B_482
      | k1_relset_1(A_483,B_482,C_484) = A_483
      | ~ v1_funct_2(C_484,A_483,B_482)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_483,B_482))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6870,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_6857])).

tff(c_6881,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6425,c_6870])).

tff(c_6882,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_6881])).

tff(c_6317,plain,(
    ! [A_430,B_431,C_432] :
      ( k2_relset_1(A_430,B_431,C_432) = k2_relat_1(C_432)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6332,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_6317])).

tff(c_6337,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6332,c_72])).

tff(c_6490,plain,(
    ! [C_443,A_444,B_445] :
      ( m1_subset_1(C_443,k1_zfmisc_1(k2_zfmisc_1(A_444,B_445)))
      | ~ r1_tarski(k2_relat_1(C_443),B_445)
      | ~ r1_tarski(k1_relat_1(C_443),A_444)
      | ~ v1_relat_1(C_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_10236,plain,(
    ! [C_643,A_644,B_645] :
      ( r1_tarski(C_643,k2_zfmisc_1(A_644,B_645))
      | ~ r1_tarski(k2_relat_1(C_643),B_645)
      | ~ r1_tarski(k1_relat_1(C_643),A_644)
      | ~ v1_relat_1(C_643) ) ),
    inference(resolution,[status(thm)],[c_6490,c_24])).

tff(c_10242,plain,(
    ! [A_644] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_644,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_644)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6337,c_10236])).

tff(c_10267,plain,(
    ! [A_646] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_646,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_646) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_6882,c_10242])).

tff(c_6424,plain,(
    ! [A_436,B_437,A_10] :
      ( k1_relset_1(A_436,B_437,A_10) = k1_relat_1(A_10)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_436,B_437)) ) ),
    inference(resolution,[status(thm)],[c_26,c_6410])).

tff(c_10273,plain,(
    ! [A_646] :
      ( k1_relset_1(A_646,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_646) ) ),
    inference(resolution,[status(thm)],[c_10267,c_6424])).

tff(c_10332,plain,(
    ! [A_648] :
      ( k1_relset_1(A_648,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_648) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6882,c_10273])).

tff(c_10337,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12,c_10332])).

tff(c_6,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6086,plain,(
    ! [C_390,B_391,A_392] :
      ( ~ v1_xboole_0(C_390)
      | ~ m1_subset_1(B_391,k1_zfmisc_1(C_390))
      | ~ r2_hidden(A_392,B_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6095,plain,(
    ! [B_393,A_394,A_395] :
      ( ~ v1_xboole_0(B_393)
      | ~ r2_hidden(A_394,A_395)
      | ~ r1_tarski(A_395,B_393) ) ),
    inference(resolution,[status(thm)],[c_26,c_6086])).

tff(c_6099,plain,(
    ! [B_396,A_397] :
      ( ~ v1_xboole_0(B_396)
      | ~ r1_tarski(A_397,B_396)
      | k1_xboole_0 = A_397 ) ),
    inference(resolution,[status(thm)],[c_6,c_6095])).

tff(c_6117,plain,
    ( ~ v1_xboole_0('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_6099])).

tff(c_6147,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6117])).

tff(c_10258,plain,(
    ! [A_644] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_644,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_644) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_6882,c_10242])).

tff(c_6727,plain,(
    ! [B_463,C_464,A_465] :
      ( k1_xboole_0 = B_463
      | v1_funct_2(C_464,A_465,B_463)
      | k1_relset_1(A_465,B_463,C_464) != A_465
      | ~ m1_subset_1(C_464,k1_zfmisc_1(k2_zfmisc_1(A_465,B_463))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_10806,plain,(
    ! [B_673,A_674,A_675] :
      ( k1_xboole_0 = B_673
      | v1_funct_2(A_674,A_675,B_673)
      | k1_relset_1(A_675,B_673,A_674) != A_675
      | ~ r1_tarski(A_674,k2_zfmisc_1(A_675,B_673)) ) ),
    inference(resolution,[status(thm)],[c_26,c_6727])).

tff(c_10841,plain,(
    ! [A_644] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_644,'#skF_4')
      | k1_relset_1(A_644,'#skF_4','#skF_5') != A_644
      | ~ r1_tarski('#skF_2',A_644) ) ),
    inference(resolution,[status(thm)],[c_10258,c_10806])).

tff(c_10898,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10841])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10991,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10898,c_2])).

tff(c_10994,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6147,c_10991])).

tff(c_11208,plain,(
    ! [A_688] :
      ( v1_funct_2('#skF_5',A_688,'#skF_4')
      | k1_relset_1(A_688,'#skF_4','#skF_5') != A_688
      | ~ r1_tarski('#skF_2',A_688) ) ),
    inference(splitRight,[status(thm)],[c_10841])).

tff(c_11214,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_11208,c_227])).

tff(c_11219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10337,c_11214])).

tff(c_11221,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_6117])).

tff(c_136,plain,(
    ! [A_49] :
      ( v1_xboole_0(k1_relat_1(A_49))
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_140,plain,(
    ! [A_49] :
      ( k1_relat_1(A_49) = k1_xboole_0
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_136,c_4])).

tff(c_11224,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11221,c_140])).

tff(c_11231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6084,c_11224])).

tff(c_11232,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6074])).

tff(c_14,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_11250,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11232,c_14])).

tff(c_240,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_253,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_72,c_240])).

tff(c_291,plain,(
    ~ r1_tarski('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_11284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11250,c_291])).

tff(c_11285,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_11661,plain,(
    ! [A_743,B_744,C_745] :
      ( k2_relset_1(A_743,B_744,C_745) = k2_relat_1(C_745)
      | ~ m1_subset_1(C_745,k1_zfmisc_1(k2_zfmisc_1(A_743,B_744))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_11668,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_11661])).

tff(c_11677,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11285,c_11668])).

tff(c_42,plain,(
    ! [A_25] :
      ( k2_relat_1(A_25) != k1_xboole_0
      | k1_xboole_0 = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_277,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_269,c_42])).

tff(c_290,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_11678,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11677,c_290])).

tff(c_11528,plain,(
    ! [A_731,B_732,C_733] :
      ( k1_relset_1(A_731,B_732,C_733) = k1_relat_1(C_733)
      | ~ m1_subset_1(C_733,k1_zfmisc_1(k2_zfmisc_1(A_731,B_732))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_11543,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_11528])).

tff(c_12135,plain,(
    ! [B_795,A_796,C_797] :
      ( k1_xboole_0 = B_795
      | k1_relset_1(A_796,B_795,C_797) = A_796
      | ~ v1_funct_2(C_797,A_796,B_795)
      | ~ m1_subset_1(C_797,k1_zfmisc_1(k2_zfmisc_1(A_796,B_795))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_12148,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_12135])).

tff(c_12159,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_11543,c_12148])).

tff(c_12160,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_12159])).

tff(c_11787,plain,(
    ! [C_760,A_761,B_762] :
      ( m1_subset_1(C_760,k1_zfmisc_1(k2_zfmisc_1(A_761,B_762)))
      | ~ r1_tarski(k2_relat_1(C_760),B_762)
      | ~ r1_tarski(k1_relat_1(C_760),A_761)
      | ~ v1_relat_1(C_760) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_50,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_relset_1(A_29,B_30,C_31) = k1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_15257,plain,(
    ! [A_947,B_948,C_949] :
      ( k1_relset_1(A_947,B_948,C_949) = k1_relat_1(C_949)
      | ~ r1_tarski(k2_relat_1(C_949),B_948)
      | ~ r1_tarski(k1_relat_1(C_949),A_947)
      | ~ v1_relat_1(C_949) ) ),
    inference(resolution,[status(thm)],[c_11787,c_50])).

tff(c_15265,plain,(
    ! [A_947,B_948] :
      ( k1_relset_1(A_947,B_948,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_4',B_948)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_947)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11677,c_15257])).

tff(c_15479,plain,(
    ! [A_957,B_958] :
      ( k1_relset_1(A_957,B_958,'#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_4',B_958)
      | ~ r1_tarski('#skF_2',A_957) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_12160,c_12160,c_15265])).

tff(c_15484,plain,(
    ! [A_959] :
      ( k1_relset_1(A_959,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_959) ) ),
    inference(resolution,[status(thm)],[c_12,c_15479])).

tff(c_15489,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12,c_15484])).

tff(c_14667,plain,(
    ! [C_913,A_914,B_915] :
      ( r1_tarski(C_913,k2_zfmisc_1(A_914,B_915))
      | ~ r1_tarski(k2_relat_1(C_913),B_915)
      | ~ r1_tarski(k1_relat_1(C_913),A_914)
      | ~ v1_relat_1(C_913) ) ),
    inference(resolution,[status(thm)],[c_11787,c_24])).

tff(c_14675,plain,(
    ! [A_914,B_915] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_914,B_915))
      | ~ r1_tarski('#skF_4',B_915)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_914)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11677,c_14667])).

tff(c_14692,plain,(
    ! [A_914,B_915] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_914,B_915))
      | ~ r1_tarski('#skF_4',B_915)
      | ~ r1_tarski('#skF_2',A_914) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_12160,c_14675])).

tff(c_11990,plain,(
    ! [B_777,C_778,A_779] :
      ( k1_xboole_0 = B_777
      | v1_funct_2(C_778,A_779,B_777)
      | k1_relset_1(A_779,B_777,C_778) != A_779
      | ~ m1_subset_1(C_778,k1_zfmisc_1(k2_zfmisc_1(A_779,B_777))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_15611,plain,(
    ! [B_964,A_965,A_966] :
      ( k1_xboole_0 = B_964
      | v1_funct_2(A_965,A_966,B_964)
      | k1_relset_1(A_966,B_964,A_965) != A_966
      | ~ r1_tarski(A_965,k2_zfmisc_1(A_966,B_964)) ) ),
    inference(resolution,[status(thm)],[c_26,c_11990])).

tff(c_16827,plain,(
    ! [B_1027,A_1028] :
      ( k1_xboole_0 = B_1027
      | v1_funct_2('#skF_5',A_1028,B_1027)
      | k1_relset_1(A_1028,B_1027,'#skF_5') != A_1028
      | ~ r1_tarski('#skF_4',B_1027)
      | ~ r1_tarski('#skF_2',A_1028) ) ),
    inference(resolution,[status(thm)],[c_14692,c_15611])).

tff(c_16841,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_16827,c_227])).

tff(c_16850,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_15489,c_16841])).

tff(c_16852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11678,c_16850])).

tff(c_16853,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_141,plain,(
    ! [A_50] :
      ( k1_relat_1(A_50) = k1_xboole_0
      | ~ v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_136,c_4])).

tff(c_149,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_141])).

tff(c_16862,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16853,c_16853,c_149])).

tff(c_276,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_269,c_44])).

tff(c_289,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_16855,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16853,c_289])).

tff(c_16905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16862,c_16855])).

tff(c_16906,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_16920,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16906,c_101])).

tff(c_16907,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_16930,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16906,c_16907])).

tff(c_17324,plain,(
    ! [A_1085,B_1086,C_1087] :
      ( k1_relset_1(A_1085,B_1086,C_1087) = k1_relat_1(C_1087)
      | ~ m1_subset_1(C_1087,k1_zfmisc_1(k2_zfmisc_1(A_1085,B_1086))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_17337,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_17324])).

tff(c_17340,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16930,c_17337])).

tff(c_66,plain,(
    ! [B_39,A_38,C_40] :
      ( k1_xboole_0 = B_39
      | k1_relset_1(A_38,B_39,C_40) = A_38
      | ~ v1_funct_2(C_40,A_38,B_39)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_17770,plain,(
    ! [B_1130,A_1131,C_1132] :
      ( B_1130 = '#skF_5'
      | k1_relset_1(A_1131,B_1130,C_1132) = A_1131
      | ~ v1_funct_2(C_1132,A_1131,B_1130)
      | ~ m1_subset_1(C_1132,k1_zfmisc_1(k2_zfmisc_1(A_1131,B_1130))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16906,c_66])).

tff(c_17789,plain,
    ( '#skF_5' = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_17770])).

tff(c_17795,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_17340,c_17789])).

tff(c_17796,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_16920,c_17795])).

tff(c_16924,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16906,c_2])).

tff(c_17834,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17796,c_16924])).

tff(c_16919,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_5',B_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16906,c_16906,c_22])).

tff(c_17828,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_2',B_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17796,c_17796,c_16919])).

tff(c_17024,plain,(
    ! [C_1041,B_1042,A_1043] :
      ( ~ v1_xboole_0(C_1041)
      | ~ m1_subset_1(B_1042,k1_zfmisc_1(C_1041))
      | ~ r2_hidden(A_1043,B_1042) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_17030,plain,(
    ! [A_1043] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_1043,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_17024])).

tff(c_17050,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_17030])).

tff(c_18040,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17828,c_17050])).

tff(c_18043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17834,c_18040])).

tff(c_18045,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_17030])).

tff(c_16922,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16906,c_4])).

tff(c_18054,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_18045,c_16922])).

tff(c_18,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18553,plain,(
    ! [B_1208,A_1209] :
      ( B_1208 = '#skF_5'
      | A_1209 = '#skF_5'
      | k2_zfmisc_1(A_1209,B_1208) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16906,c_16906,c_16906,c_18])).

tff(c_18556,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_18054,c_18553])).

tff(c_18565,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_16920,c_18556])).

tff(c_18597,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18565,c_18565,c_16930])).

tff(c_18070,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18054,c_74])).

tff(c_18587,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18565,c_18565,c_18070])).

tff(c_18360,plain,(
    ! [A_1183,B_1184,C_1185] :
      ( k1_relset_1(A_1183,B_1184,C_1185) = k1_relat_1(C_1185)
      | ~ m1_subset_1(C_1185,k1_zfmisc_1(k2_zfmisc_1(A_1183,B_1184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_18366,plain,(
    ! [B_9,C_1185] :
      ( k1_relset_1('#skF_5',B_9,C_1185) = k1_relat_1(C_1185)
      | ~ m1_subset_1(C_1185,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16919,c_18360])).

tff(c_19682,plain,(
    ! [B_1289,C_1290] :
      ( k1_relset_1('#skF_2',B_1289,C_1290) = k1_relat_1(C_1290)
      | ~ m1_subset_1(C_1290,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18565,c_18565,c_18366])).

tff(c_19684,plain,(
    ! [B_1289] : k1_relset_1('#skF_2',B_1289,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18587,c_19682])).

tff(c_19689,plain,(
    ! [B_1289] : k1_relset_1('#skF_2',B_1289,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18597,c_19684])).

tff(c_18600,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18565,c_16906])).

tff(c_60,plain,(
    ! [C_40,B_39] :
      ( v1_funct_2(C_40,k1_xboole_0,B_39)
      | k1_relset_1(k1_xboole_0,B_39,C_40) != k1_xboole_0
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_82,plain,(
    ! [C_40,B_39] :
      ( v1_funct_2(C_40,k1_xboole_0,B_39)
      | k1_relset_1(k1_xboole_0,B_39,C_40) != k1_xboole_0
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_60])).

tff(c_18701,plain,(
    ! [C_1219,B_1220] :
      ( v1_funct_2(C_1219,'#skF_2',B_1220)
      | k1_relset_1('#skF_2',B_1220,C_1219) != '#skF_2'
      | ~ m1_subset_1(C_1219,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18600,c_18600,c_18600,c_18600,c_82])).

tff(c_18967,plain,(
    ! [B_1231] :
      ( v1_funct_2('#skF_2','#skF_2',B_1231)
      | k1_relset_1('#skF_2',B_1231,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_18587,c_18701])).

tff(c_18602,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18565,c_227])).

tff(c_18973,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_2') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_18967,c_18602])).

tff(c_19696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19689,c_18973])).

tff(c_19697,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_20399,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20379,c_19697])).

tff(c_20422,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19725,c_20100,c_20399])).

tff(c_20426,plain,
    ( ~ v4_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_20422])).

tff(c_20430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19725,c_19946,c_20426])).

tff(c_20432,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_20431,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_20441,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20432,c_20431])).

tff(c_20436,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20431,c_2])).

tff(c_20446,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20441,c_20436])).

tff(c_20492,plain,(
    ! [A_1380] :
      ( v1_xboole_0(k1_relat_1(A_1380))
      | ~ v1_xboole_0(A_1380) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20434,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20431,c_4])).

tff(c_20455,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20441,c_20434])).

tff(c_20511,plain,(
    ! [A_1382] :
      ( k1_relat_1(A_1382) = '#skF_3'
      | ~ v1_xboole_0(A_1382) ) ),
    inference(resolution,[status(thm)],[c_20492,c_20455])).

tff(c_20519,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20446,c_20511])).

tff(c_20463,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_3',B_9) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20432,c_20432,c_22])).

tff(c_20529,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20463,c_20441,c_74])).

tff(c_20580,plain,(
    ! [A_1389,B_1390] :
      ( r1_tarski(A_1389,B_1390)
      | ~ m1_subset_1(A_1389,k1_zfmisc_1(B_1390)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20588,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_20529,c_20580])).

tff(c_16,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20497,plain,(
    ! [A_7] :
      ( A_7 = '#skF_3'
      | ~ r1_tarski(A_7,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20432,c_20432,c_16])).

tff(c_20592,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20588,c_20497])).

tff(c_20595,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20592,c_20529])).

tff(c_20933,plain,(
    ! [A_1442,B_1443,C_1444] :
      ( k1_relset_1(A_1442,B_1443,C_1444) = k1_relat_1(C_1444)
      | ~ m1_subset_1(C_1444,k1_zfmisc_1(k2_zfmisc_1(A_1442,B_1443))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_21366,plain,(
    ! [B_1490,C_1491] :
      ( k1_relset_1('#skF_3',B_1490,C_1491) = k1_relat_1(C_1491)
      | ~ m1_subset_1(C_1491,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20463,c_20933])).

tff(c_21368,plain,(
    ! [B_1490] : k1_relset_1('#skF_3',B_1490,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20595,c_21366])).

tff(c_21373,plain,(
    ! [B_1490] : k1_relset_1('#skF_3',B_1490,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20519,c_21368])).

tff(c_21341,plain,(
    ! [C_1487,B_1488] :
      ( v1_funct_2(C_1487,'#skF_3',B_1488)
      | k1_relset_1('#skF_3',B_1488,C_1487) != '#skF_3'
      | ~ m1_subset_1(C_1487,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20432,c_20432,c_20432,c_20432,c_82])).

tff(c_21349,plain,(
    ! [B_1489] :
      ( v1_funct_2('#skF_3','#skF_3',B_1489)
      | k1_relset_1('#skF_3',B_1489,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_20595,c_21341])).

tff(c_20531,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20441,c_20529,c_20463,c_20441,c_80])).

tff(c_20594,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20592,c_20531])).

tff(c_21365,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_21349,c_20594])).

tff(c_21379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21373,c_21365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:34:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.94/3.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.15/3.70  
% 10.15/3.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.15/3.71  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 10.15/3.71  
% 10.15/3.71  %Foreground sorts:
% 10.15/3.71  
% 10.15/3.71  
% 10.15/3.71  %Background operators:
% 10.15/3.71  
% 10.15/3.71  
% 10.15/3.71  %Foreground operators:
% 10.15/3.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.15/3.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.15/3.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.15/3.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.15/3.71  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.15/3.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.15/3.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.15/3.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.15/3.71  tff('#skF_5', type, '#skF_5': $i).
% 10.15/3.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.15/3.71  tff('#skF_2', type, '#skF_2': $i).
% 10.15/3.71  tff('#skF_3', type, '#skF_3': $i).
% 10.15/3.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.15/3.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.15/3.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.15/3.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.15/3.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.15/3.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.15/3.71  tff('#skF_4', type, '#skF_4': $i).
% 10.15/3.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.15/3.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.15/3.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.15/3.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.15/3.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.15/3.71  
% 10.15/3.74  tff(f_86, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.15/3.74  tff(f_156, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 10.15/3.74  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.15/3.74  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.15/3.74  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 10.15/3.74  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.15/3.74  tff(f_118, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 10.15/3.74  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.15/3.74  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.15/3.74  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.15/3.74  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.15/3.74  tff(f_56, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.15/3.74  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 10.15/3.74  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 10.15/3.74  tff(f_67, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 10.15/3.74  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.15/3.74  tff(f_84, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 10.15/3.74  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.15/3.74  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.15/3.74  tff(f_50, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 10.15/3.74  tff(c_38, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.15/3.74  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.15/3.74  tff(c_19715, plain, (![B_1292, A_1293]: (v1_relat_1(B_1292) | ~m1_subset_1(B_1292, k1_zfmisc_1(A_1293)) | ~v1_relat_1(A_1293))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.15/3.74  tff(c_19721, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_19715])).
% 10.15/3.74  tff(c_19725, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_19721])).
% 10.15/3.74  tff(c_19931, plain, (![C_1325, A_1326, B_1327]: (v4_relat_1(C_1325, A_1326) | ~m1_subset_1(C_1325, k1_zfmisc_1(k2_zfmisc_1(A_1326, B_1327))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.15/3.74  tff(c_19946, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_19931])).
% 10.15/3.74  tff(c_34, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.15/3.74  tff(c_20083, plain, (![A_1346, B_1347, C_1348]: (k2_relset_1(A_1346, B_1347, C_1348)=k2_relat_1(C_1348) | ~m1_subset_1(C_1348, k1_zfmisc_1(k2_zfmisc_1(A_1346, B_1347))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.15/3.74  tff(c_20098, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_20083])).
% 10.15/3.74  tff(c_72, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.15/3.74  tff(c_20100, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20098, c_72])).
% 10.15/3.74  tff(c_20379, plain, (![C_1371, A_1372, B_1373]: (m1_subset_1(C_1371, k1_zfmisc_1(k2_zfmisc_1(A_1372, B_1373))) | ~r1_tarski(k2_relat_1(C_1371), B_1373) | ~r1_tarski(k1_relat_1(C_1371), A_1372) | ~v1_relat_1(C_1371))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.15/3.74  tff(c_12, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.15/3.74  tff(c_70, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.15/3.74  tff(c_101, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_70])).
% 10.15/3.74  tff(c_76, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.15/3.74  tff(c_610, plain, (![A_114, B_115, C_116]: (k1_relset_1(A_114, B_115, C_116)=k1_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.15/3.74  tff(c_625, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_610])).
% 10.15/3.74  tff(c_1057, plain, (![B_159, A_160, C_161]: (k1_xboole_0=B_159 | k1_relset_1(A_160, B_159, C_161)=A_160 | ~v1_funct_2(C_161, A_160, B_159) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.15/3.74  tff(c_1070, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_1057])).
% 10.15/3.74  tff(c_1081, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_625, c_1070])).
% 10.15/3.74  tff(c_1082, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_101, c_1081])).
% 10.15/3.74  tff(c_259, plain, (![B_63, A_64]: (v1_relat_1(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.15/3.74  tff(c_265, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_259])).
% 10.15/3.74  tff(c_269, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_265])).
% 10.15/3.74  tff(c_671, plain, (![A_121, B_122, C_123]: (k2_relset_1(A_121, B_122, C_123)=k2_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.15/3.74  tff(c_686, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_671])).
% 10.15/3.74  tff(c_688, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_686, c_72])).
% 10.15/3.74  tff(c_920, plain, (![C_143, A_144, B_145]: (m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~r1_tarski(k2_relat_1(C_143), B_145) | ~r1_tarski(k1_relat_1(C_143), A_144) | ~v1_relat_1(C_143))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.15/3.74  tff(c_24, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.15/3.74  tff(c_4685, plain, (![C_338, A_339, B_340]: (r1_tarski(C_338, k2_zfmisc_1(A_339, B_340)) | ~r1_tarski(k2_relat_1(C_338), B_340) | ~r1_tarski(k1_relat_1(C_338), A_339) | ~v1_relat_1(C_338))), inference(resolution, [status(thm)], [c_920, c_24])).
% 10.15/3.74  tff(c_4693, plain, (![A_339]: (r1_tarski('#skF_5', k2_zfmisc_1(A_339, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), A_339) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_688, c_4685])).
% 10.15/3.74  tff(c_4720, plain, (![A_341]: (r1_tarski('#skF_5', k2_zfmisc_1(A_341, '#skF_4')) | ~r1_tarski('#skF_2', A_341))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_1082, c_4693])).
% 10.15/3.74  tff(c_26, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.15/3.74  tff(c_624, plain, (![A_114, B_115, A_10]: (k1_relset_1(A_114, B_115, A_10)=k1_relat_1(A_10) | ~r1_tarski(A_10, k2_zfmisc_1(A_114, B_115)))), inference(resolution, [status(thm)], [c_26, c_610])).
% 10.15/3.74  tff(c_4723, plain, (![A_341]: (k1_relset_1(A_341, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_341))), inference(resolution, [status(thm)], [c_4720, c_624])).
% 10.15/3.74  tff(c_4785, plain, (![A_343]: (k1_relset_1(A_343, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_343))), inference(demodulation, [status(thm), theory('equality')], [c_1082, c_4723])).
% 10.15/3.74  tff(c_4790, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_12, c_4785])).
% 10.15/3.74  tff(c_292, plain, (![A_67, B_68]: (v1_relat_1(A_67) | ~v1_relat_1(B_68) | ~r1_tarski(A_67, B_68))), inference(resolution, [status(thm)], [c_26, c_259])).
% 10.15/3.74  tff(c_312, plain, (v1_relat_1(k2_relset_1('#skF_2', '#skF_3', '#skF_5')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_292])).
% 10.15/3.74  tff(c_334, plain, (~v1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_312])).
% 10.15/3.74  tff(c_4711, plain, (![A_339]: (r1_tarski('#skF_5', k2_zfmisc_1(A_339, '#skF_4')) | ~r1_tarski('#skF_2', A_339))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_1082, c_4693])).
% 10.15/3.74  tff(c_1177, plain, (![B_168, C_169, A_170]: (k1_xboole_0=B_168 | v1_funct_2(C_169, A_170, B_168) | k1_relset_1(A_170, B_168, C_169)!=A_170 | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_170, B_168))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.15/3.74  tff(c_5516, plain, (![B_371, A_372, A_373]: (k1_xboole_0=B_371 | v1_funct_2(A_372, A_373, B_371) | k1_relset_1(A_373, B_371, A_372)!=A_373 | ~r1_tarski(A_372, k2_zfmisc_1(A_373, B_371)))), inference(resolution, [status(thm)], [c_26, c_1177])).
% 10.15/3.74  tff(c_5555, plain, (![A_339]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_339, '#skF_4') | k1_relset_1(A_339, '#skF_4', '#skF_5')!=A_339 | ~r1_tarski('#skF_2', A_339))), inference(resolution, [status(thm)], [c_4711, c_5516])).
% 10.15/3.74  tff(c_5709, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_5555])).
% 10.15/3.74  tff(c_22, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.15/3.74  tff(c_117, plain, (![A_46, B_47]: (v1_relat_1(k2_zfmisc_1(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.15/3.74  tff(c_119, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_117])).
% 10.15/3.74  tff(c_5797, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5709, c_119])).
% 10.15/3.74  tff(c_5805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_5797])).
% 10.15/3.74  tff(c_6054, plain, (![A_389]: (v1_funct_2('#skF_5', A_389, '#skF_4') | k1_relset_1(A_389, '#skF_4', '#skF_5')!=A_389 | ~r1_tarski('#skF_2', A_389))), inference(splitRight, [status(thm)], [c_5555])).
% 10.15/3.74  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.15/3.74  tff(c_68, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.15/3.74  tff(c_80, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_68])).
% 10.15/3.74  tff(c_227, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_80])).
% 10.15/3.74  tff(c_6060, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_6054, c_227])).
% 10.15/3.74  tff(c_6065, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4790, c_6060])).
% 10.15/3.74  tff(c_6067, plain, (v1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_312])).
% 10.15/3.74  tff(c_44, plain, (![A_25]: (k1_relat_1(A_25)!=k1_xboole_0 | k1_xboole_0=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.15/3.74  tff(c_6074, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_6067, c_44])).
% 10.15/3.74  tff(c_6084, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6074])).
% 10.15/3.74  tff(c_6410, plain, (![A_436, B_437, C_438]: (k1_relset_1(A_436, B_437, C_438)=k1_relat_1(C_438) | ~m1_subset_1(C_438, k1_zfmisc_1(k2_zfmisc_1(A_436, B_437))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.15/3.74  tff(c_6425, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_6410])).
% 10.15/3.74  tff(c_6857, plain, (![B_482, A_483, C_484]: (k1_xboole_0=B_482 | k1_relset_1(A_483, B_482, C_484)=A_483 | ~v1_funct_2(C_484, A_483, B_482) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_483, B_482))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.15/3.74  tff(c_6870, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_6857])).
% 10.15/3.74  tff(c_6881, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_6425, c_6870])).
% 10.15/3.74  tff(c_6882, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_101, c_6881])).
% 10.15/3.74  tff(c_6317, plain, (![A_430, B_431, C_432]: (k2_relset_1(A_430, B_431, C_432)=k2_relat_1(C_432) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.15/3.74  tff(c_6332, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_6317])).
% 10.15/3.74  tff(c_6337, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6332, c_72])).
% 10.15/3.74  tff(c_6490, plain, (![C_443, A_444, B_445]: (m1_subset_1(C_443, k1_zfmisc_1(k2_zfmisc_1(A_444, B_445))) | ~r1_tarski(k2_relat_1(C_443), B_445) | ~r1_tarski(k1_relat_1(C_443), A_444) | ~v1_relat_1(C_443))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.15/3.74  tff(c_10236, plain, (![C_643, A_644, B_645]: (r1_tarski(C_643, k2_zfmisc_1(A_644, B_645)) | ~r1_tarski(k2_relat_1(C_643), B_645) | ~r1_tarski(k1_relat_1(C_643), A_644) | ~v1_relat_1(C_643))), inference(resolution, [status(thm)], [c_6490, c_24])).
% 10.15/3.74  tff(c_10242, plain, (![A_644]: (r1_tarski('#skF_5', k2_zfmisc_1(A_644, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), A_644) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_6337, c_10236])).
% 10.15/3.74  tff(c_10267, plain, (![A_646]: (r1_tarski('#skF_5', k2_zfmisc_1(A_646, '#skF_4')) | ~r1_tarski('#skF_2', A_646))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_6882, c_10242])).
% 10.15/3.74  tff(c_6424, plain, (![A_436, B_437, A_10]: (k1_relset_1(A_436, B_437, A_10)=k1_relat_1(A_10) | ~r1_tarski(A_10, k2_zfmisc_1(A_436, B_437)))), inference(resolution, [status(thm)], [c_26, c_6410])).
% 10.15/3.74  tff(c_10273, plain, (![A_646]: (k1_relset_1(A_646, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_646))), inference(resolution, [status(thm)], [c_10267, c_6424])).
% 10.15/3.74  tff(c_10332, plain, (![A_648]: (k1_relset_1(A_648, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_648))), inference(demodulation, [status(thm), theory('equality')], [c_6882, c_10273])).
% 10.15/3.74  tff(c_10337, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_12, c_10332])).
% 10.15/3.74  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.15/3.74  tff(c_6086, plain, (![C_390, B_391, A_392]: (~v1_xboole_0(C_390) | ~m1_subset_1(B_391, k1_zfmisc_1(C_390)) | ~r2_hidden(A_392, B_391))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.15/3.74  tff(c_6095, plain, (![B_393, A_394, A_395]: (~v1_xboole_0(B_393) | ~r2_hidden(A_394, A_395) | ~r1_tarski(A_395, B_393))), inference(resolution, [status(thm)], [c_26, c_6086])).
% 10.15/3.74  tff(c_6099, plain, (![B_396, A_397]: (~v1_xboole_0(B_396) | ~r1_tarski(A_397, B_396) | k1_xboole_0=A_397)), inference(resolution, [status(thm)], [c_6, c_6095])).
% 10.15/3.74  tff(c_6117, plain, (~v1_xboole_0('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_6099])).
% 10.15/3.74  tff(c_6147, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_6117])).
% 10.15/3.74  tff(c_10258, plain, (![A_644]: (r1_tarski('#skF_5', k2_zfmisc_1(A_644, '#skF_4')) | ~r1_tarski('#skF_2', A_644))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_6882, c_10242])).
% 10.15/3.74  tff(c_6727, plain, (![B_463, C_464, A_465]: (k1_xboole_0=B_463 | v1_funct_2(C_464, A_465, B_463) | k1_relset_1(A_465, B_463, C_464)!=A_465 | ~m1_subset_1(C_464, k1_zfmisc_1(k2_zfmisc_1(A_465, B_463))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.15/3.74  tff(c_10806, plain, (![B_673, A_674, A_675]: (k1_xboole_0=B_673 | v1_funct_2(A_674, A_675, B_673) | k1_relset_1(A_675, B_673, A_674)!=A_675 | ~r1_tarski(A_674, k2_zfmisc_1(A_675, B_673)))), inference(resolution, [status(thm)], [c_26, c_6727])).
% 10.15/3.74  tff(c_10841, plain, (![A_644]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_644, '#skF_4') | k1_relset_1(A_644, '#skF_4', '#skF_5')!=A_644 | ~r1_tarski('#skF_2', A_644))), inference(resolution, [status(thm)], [c_10258, c_10806])).
% 10.15/3.74  tff(c_10898, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_10841])).
% 10.15/3.74  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 10.15/3.74  tff(c_10991, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10898, c_2])).
% 10.15/3.74  tff(c_10994, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6147, c_10991])).
% 10.15/3.74  tff(c_11208, plain, (![A_688]: (v1_funct_2('#skF_5', A_688, '#skF_4') | k1_relset_1(A_688, '#skF_4', '#skF_5')!=A_688 | ~r1_tarski('#skF_2', A_688))), inference(splitRight, [status(thm)], [c_10841])).
% 10.15/3.74  tff(c_11214, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_11208, c_227])).
% 10.15/3.74  tff(c_11219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10337, c_11214])).
% 10.15/3.74  tff(c_11221, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_6117])).
% 10.15/3.74  tff(c_136, plain, (![A_49]: (v1_xboole_0(k1_relat_1(A_49)) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.15/3.74  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 10.15/3.74  tff(c_140, plain, (![A_49]: (k1_relat_1(A_49)=k1_xboole_0 | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_136, c_4])).
% 10.15/3.74  tff(c_11224, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_11221, c_140])).
% 10.15/3.74  tff(c_11231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6084, c_11224])).
% 10.15/3.74  tff(c_11232, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_6074])).
% 10.15/3.74  tff(c_14, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.15/3.74  tff(c_11250, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_11232, c_14])).
% 10.15/3.74  tff(c_240, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.15/3.74  tff(c_253, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_72, c_240])).
% 10.15/3.74  tff(c_291, plain, (~r1_tarski('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_253])).
% 10.15/3.74  tff(c_11284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11250, c_291])).
% 10.15/3.74  tff(c_11285, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_253])).
% 10.15/3.74  tff(c_11661, plain, (![A_743, B_744, C_745]: (k2_relset_1(A_743, B_744, C_745)=k2_relat_1(C_745) | ~m1_subset_1(C_745, k1_zfmisc_1(k2_zfmisc_1(A_743, B_744))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.15/3.74  tff(c_11668, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_11661])).
% 10.15/3.74  tff(c_11677, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11285, c_11668])).
% 10.15/3.74  tff(c_42, plain, (![A_25]: (k2_relat_1(A_25)!=k1_xboole_0 | k1_xboole_0=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.15/3.74  tff(c_277, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_269, c_42])).
% 10.15/3.74  tff(c_290, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_277])).
% 10.15/3.74  tff(c_11678, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11677, c_290])).
% 10.15/3.74  tff(c_11528, plain, (![A_731, B_732, C_733]: (k1_relset_1(A_731, B_732, C_733)=k1_relat_1(C_733) | ~m1_subset_1(C_733, k1_zfmisc_1(k2_zfmisc_1(A_731, B_732))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.15/3.74  tff(c_11543, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_11528])).
% 10.15/3.74  tff(c_12135, plain, (![B_795, A_796, C_797]: (k1_xboole_0=B_795 | k1_relset_1(A_796, B_795, C_797)=A_796 | ~v1_funct_2(C_797, A_796, B_795) | ~m1_subset_1(C_797, k1_zfmisc_1(k2_zfmisc_1(A_796, B_795))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.15/3.74  tff(c_12148, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_12135])).
% 10.15/3.74  tff(c_12159, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_11543, c_12148])).
% 10.15/3.74  tff(c_12160, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_101, c_12159])).
% 10.15/3.74  tff(c_11787, plain, (![C_760, A_761, B_762]: (m1_subset_1(C_760, k1_zfmisc_1(k2_zfmisc_1(A_761, B_762))) | ~r1_tarski(k2_relat_1(C_760), B_762) | ~r1_tarski(k1_relat_1(C_760), A_761) | ~v1_relat_1(C_760))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.15/3.74  tff(c_50, plain, (![A_29, B_30, C_31]: (k1_relset_1(A_29, B_30, C_31)=k1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.15/3.74  tff(c_15257, plain, (![A_947, B_948, C_949]: (k1_relset_1(A_947, B_948, C_949)=k1_relat_1(C_949) | ~r1_tarski(k2_relat_1(C_949), B_948) | ~r1_tarski(k1_relat_1(C_949), A_947) | ~v1_relat_1(C_949))), inference(resolution, [status(thm)], [c_11787, c_50])).
% 10.15/3.74  tff(c_15265, plain, (![A_947, B_948]: (k1_relset_1(A_947, B_948, '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_4', B_948) | ~r1_tarski(k1_relat_1('#skF_5'), A_947) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11677, c_15257])).
% 10.15/3.74  tff(c_15479, plain, (![A_957, B_958]: (k1_relset_1(A_957, B_958, '#skF_5')='#skF_2' | ~r1_tarski('#skF_4', B_958) | ~r1_tarski('#skF_2', A_957))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_12160, c_12160, c_15265])).
% 10.15/3.74  tff(c_15484, plain, (![A_959]: (k1_relset_1(A_959, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_959))), inference(resolution, [status(thm)], [c_12, c_15479])).
% 10.15/3.74  tff(c_15489, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_12, c_15484])).
% 10.15/3.74  tff(c_14667, plain, (![C_913, A_914, B_915]: (r1_tarski(C_913, k2_zfmisc_1(A_914, B_915)) | ~r1_tarski(k2_relat_1(C_913), B_915) | ~r1_tarski(k1_relat_1(C_913), A_914) | ~v1_relat_1(C_913))), inference(resolution, [status(thm)], [c_11787, c_24])).
% 10.15/3.74  tff(c_14675, plain, (![A_914, B_915]: (r1_tarski('#skF_5', k2_zfmisc_1(A_914, B_915)) | ~r1_tarski('#skF_4', B_915) | ~r1_tarski(k1_relat_1('#skF_5'), A_914) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11677, c_14667])).
% 10.15/3.74  tff(c_14692, plain, (![A_914, B_915]: (r1_tarski('#skF_5', k2_zfmisc_1(A_914, B_915)) | ~r1_tarski('#skF_4', B_915) | ~r1_tarski('#skF_2', A_914))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_12160, c_14675])).
% 10.15/3.74  tff(c_11990, plain, (![B_777, C_778, A_779]: (k1_xboole_0=B_777 | v1_funct_2(C_778, A_779, B_777) | k1_relset_1(A_779, B_777, C_778)!=A_779 | ~m1_subset_1(C_778, k1_zfmisc_1(k2_zfmisc_1(A_779, B_777))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.15/3.74  tff(c_15611, plain, (![B_964, A_965, A_966]: (k1_xboole_0=B_964 | v1_funct_2(A_965, A_966, B_964) | k1_relset_1(A_966, B_964, A_965)!=A_966 | ~r1_tarski(A_965, k2_zfmisc_1(A_966, B_964)))), inference(resolution, [status(thm)], [c_26, c_11990])).
% 10.15/3.74  tff(c_16827, plain, (![B_1027, A_1028]: (k1_xboole_0=B_1027 | v1_funct_2('#skF_5', A_1028, B_1027) | k1_relset_1(A_1028, B_1027, '#skF_5')!=A_1028 | ~r1_tarski('#skF_4', B_1027) | ~r1_tarski('#skF_2', A_1028))), inference(resolution, [status(thm)], [c_14692, c_15611])).
% 10.15/3.74  tff(c_16841, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_16827, c_227])).
% 10.15/3.74  tff(c_16850, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_15489, c_16841])).
% 10.15/3.74  tff(c_16852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11678, c_16850])).
% 10.15/3.74  tff(c_16853, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_277])).
% 10.15/3.74  tff(c_141, plain, (![A_50]: (k1_relat_1(A_50)=k1_xboole_0 | ~v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_136, c_4])).
% 10.15/3.74  tff(c_149, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_141])).
% 10.15/3.74  tff(c_16862, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16853, c_16853, c_149])).
% 10.15/3.74  tff(c_276, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_269, c_44])).
% 10.15/3.74  tff(c_289, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_276])).
% 10.15/3.74  tff(c_16855, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16853, c_289])).
% 10.15/3.74  tff(c_16905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16862, c_16855])).
% 10.15/3.74  tff(c_16906, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_276])).
% 10.15/3.74  tff(c_16920, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16906, c_101])).
% 10.15/3.74  tff(c_16907, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_276])).
% 10.15/3.74  tff(c_16930, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16906, c_16907])).
% 10.15/3.74  tff(c_17324, plain, (![A_1085, B_1086, C_1087]: (k1_relset_1(A_1085, B_1086, C_1087)=k1_relat_1(C_1087) | ~m1_subset_1(C_1087, k1_zfmisc_1(k2_zfmisc_1(A_1085, B_1086))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.15/3.74  tff(c_17337, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_17324])).
% 10.15/3.74  tff(c_17340, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16930, c_17337])).
% 10.15/3.74  tff(c_66, plain, (![B_39, A_38, C_40]: (k1_xboole_0=B_39 | k1_relset_1(A_38, B_39, C_40)=A_38 | ~v1_funct_2(C_40, A_38, B_39) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.15/3.74  tff(c_17770, plain, (![B_1130, A_1131, C_1132]: (B_1130='#skF_5' | k1_relset_1(A_1131, B_1130, C_1132)=A_1131 | ~v1_funct_2(C_1132, A_1131, B_1130) | ~m1_subset_1(C_1132, k1_zfmisc_1(k2_zfmisc_1(A_1131, B_1130))))), inference(demodulation, [status(thm), theory('equality')], [c_16906, c_66])).
% 10.15/3.74  tff(c_17789, plain, ('#skF_5'='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_17770])).
% 10.15/3.74  tff(c_17795, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_17340, c_17789])).
% 10.15/3.74  tff(c_17796, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_16920, c_17795])).
% 10.15/3.74  tff(c_16924, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16906, c_2])).
% 10.15/3.74  tff(c_17834, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17796, c_16924])).
% 10.15/3.74  tff(c_16919, plain, (![B_9]: (k2_zfmisc_1('#skF_5', B_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16906, c_16906, c_22])).
% 10.15/3.74  tff(c_17828, plain, (![B_9]: (k2_zfmisc_1('#skF_2', B_9)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17796, c_17796, c_16919])).
% 10.15/3.74  tff(c_17024, plain, (![C_1041, B_1042, A_1043]: (~v1_xboole_0(C_1041) | ~m1_subset_1(B_1042, k1_zfmisc_1(C_1041)) | ~r2_hidden(A_1043, B_1042))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.15/3.74  tff(c_17030, plain, (![A_1043]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_1043, '#skF_5'))), inference(resolution, [status(thm)], [c_74, c_17024])).
% 10.15/3.74  tff(c_17050, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_17030])).
% 10.15/3.74  tff(c_18040, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17828, c_17050])).
% 10.15/3.74  tff(c_18043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17834, c_18040])).
% 10.15/3.74  tff(c_18045, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_17030])).
% 10.15/3.74  tff(c_16922, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_16906, c_4])).
% 10.15/3.74  tff(c_18054, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_18045, c_16922])).
% 10.15/3.74  tff(c_18, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.15/3.74  tff(c_18553, plain, (![B_1208, A_1209]: (B_1208='#skF_5' | A_1209='#skF_5' | k2_zfmisc_1(A_1209, B_1208)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16906, c_16906, c_16906, c_18])).
% 10.15/3.74  tff(c_18556, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_18054, c_18553])).
% 10.15/3.74  tff(c_18565, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_16920, c_18556])).
% 10.15/3.74  tff(c_18597, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18565, c_18565, c_16930])).
% 10.15/3.74  tff(c_18070, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_18054, c_74])).
% 10.15/3.74  tff(c_18587, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18565, c_18565, c_18070])).
% 10.15/3.74  tff(c_18360, plain, (![A_1183, B_1184, C_1185]: (k1_relset_1(A_1183, B_1184, C_1185)=k1_relat_1(C_1185) | ~m1_subset_1(C_1185, k1_zfmisc_1(k2_zfmisc_1(A_1183, B_1184))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.15/3.74  tff(c_18366, plain, (![B_9, C_1185]: (k1_relset_1('#skF_5', B_9, C_1185)=k1_relat_1(C_1185) | ~m1_subset_1(C_1185, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_16919, c_18360])).
% 10.15/3.74  tff(c_19682, plain, (![B_1289, C_1290]: (k1_relset_1('#skF_2', B_1289, C_1290)=k1_relat_1(C_1290) | ~m1_subset_1(C_1290, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18565, c_18565, c_18366])).
% 10.15/3.74  tff(c_19684, plain, (![B_1289]: (k1_relset_1('#skF_2', B_1289, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_18587, c_19682])).
% 10.15/3.74  tff(c_19689, plain, (![B_1289]: (k1_relset_1('#skF_2', B_1289, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18597, c_19684])).
% 10.15/3.74  tff(c_18600, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18565, c_16906])).
% 10.15/3.74  tff(c_60, plain, (![C_40, B_39]: (v1_funct_2(C_40, k1_xboole_0, B_39) | k1_relset_1(k1_xboole_0, B_39, C_40)!=k1_xboole_0 | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_39))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.15/3.74  tff(c_82, plain, (![C_40, B_39]: (v1_funct_2(C_40, k1_xboole_0, B_39) | k1_relset_1(k1_xboole_0, B_39, C_40)!=k1_xboole_0 | ~m1_subset_1(C_40, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_60])).
% 10.15/3.74  tff(c_18701, plain, (![C_1219, B_1220]: (v1_funct_2(C_1219, '#skF_2', B_1220) | k1_relset_1('#skF_2', B_1220, C_1219)!='#skF_2' | ~m1_subset_1(C_1219, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18600, c_18600, c_18600, c_18600, c_82])).
% 10.15/3.74  tff(c_18967, plain, (![B_1231]: (v1_funct_2('#skF_2', '#skF_2', B_1231) | k1_relset_1('#skF_2', B_1231, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_18587, c_18701])).
% 10.15/3.74  tff(c_18602, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18565, c_227])).
% 10.15/3.74  tff(c_18973, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_2')!='#skF_2'), inference(resolution, [status(thm)], [c_18967, c_18602])).
% 10.15/3.74  tff(c_19696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19689, c_18973])).
% 10.15/3.74  tff(c_19697, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_80])).
% 10.15/3.74  tff(c_20399, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20379, c_19697])).
% 10.15/3.74  tff(c_20422, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19725, c_20100, c_20399])).
% 10.15/3.74  tff(c_20426, plain, (~v4_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_20422])).
% 10.15/3.74  tff(c_20430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19725, c_19946, c_20426])).
% 10.15/3.74  tff(c_20432, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_70])).
% 10.15/3.74  tff(c_20431, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_70])).
% 10.15/3.74  tff(c_20441, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20432, c_20431])).
% 10.15/3.74  tff(c_20436, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20431, c_2])).
% 10.15/3.74  tff(c_20446, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20441, c_20436])).
% 10.15/3.74  tff(c_20492, plain, (![A_1380]: (v1_xboole_0(k1_relat_1(A_1380)) | ~v1_xboole_0(A_1380))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.15/3.74  tff(c_20434, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_20431, c_4])).
% 10.15/3.74  tff(c_20455, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_20441, c_20434])).
% 10.15/3.74  tff(c_20511, plain, (![A_1382]: (k1_relat_1(A_1382)='#skF_3' | ~v1_xboole_0(A_1382))), inference(resolution, [status(thm)], [c_20492, c_20455])).
% 10.15/3.74  tff(c_20519, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_20446, c_20511])).
% 10.15/3.74  tff(c_20463, plain, (![B_9]: (k2_zfmisc_1('#skF_3', B_9)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20432, c_20432, c_22])).
% 10.15/3.74  tff(c_20529, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20463, c_20441, c_74])).
% 10.15/3.74  tff(c_20580, plain, (![A_1389, B_1390]: (r1_tarski(A_1389, B_1390) | ~m1_subset_1(A_1389, k1_zfmisc_1(B_1390)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.15/3.74  tff(c_20588, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_20529, c_20580])).
% 10.15/3.74  tff(c_16, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.15/3.74  tff(c_20497, plain, (![A_7]: (A_7='#skF_3' | ~r1_tarski(A_7, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20432, c_20432, c_16])).
% 10.15/3.74  tff(c_20592, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_20588, c_20497])).
% 10.15/3.74  tff(c_20595, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20592, c_20529])).
% 10.15/3.74  tff(c_20933, plain, (![A_1442, B_1443, C_1444]: (k1_relset_1(A_1442, B_1443, C_1444)=k1_relat_1(C_1444) | ~m1_subset_1(C_1444, k1_zfmisc_1(k2_zfmisc_1(A_1442, B_1443))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.15/3.74  tff(c_21366, plain, (![B_1490, C_1491]: (k1_relset_1('#skF_3', B_1490, C_1491)=k1_relat_1(C_1491) | ~m1_subset_1(C_1491, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_20463, c_20933])).
% 10.15/3.74  tff(c_21368, plain, (![B_1490]: (k1_relset_1('#skF_3', B_1490, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_20595, c_21366])).
% 10.15/3.74  tff(c_21373, plain, (![B_1490]: (k1_relset_1('#skF_3', B_1490, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20519, c_21368])).
% 10.15/3.74  tff(c_21341, plain, (![C_1487, B_1488]: (v1_funct_2(C_1487, '#skF_3', B_1488) | k1_relset_1('#skF_3', B_1488, C_1487)!='#skF_3' | ~m1_subset_1(C_1487, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_20432, c_20432, c_20432, c_20432, c_82])).
% 10.15/3.74  tff(c_21349, plain, (![B_1489]: (v1_funct_2('#skF_3', '#skF_3', B_1489) | k1_relset_1('#skF_3', B_1489, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_20595, c_21341])).
% 10.15/3.74  tff(c_20531, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20441, c_20529, c_20463, c_20441, c_80])).
% 10.15/3.74  tff(c_20594, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20592, c_20531])).
% 10.15/3.74  tff(c_21365, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_21349, c_20594])).
% 10.15/3.74  tff(c_21379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21373, c_21365])).
% 10.15/3.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.15/3.74  
% 10.15/3.74  Inference rules
% 10.15/3.74  ----------------------
% 10.15/3.74  #Ref     : 0
% 10.15/3.74  #Sup     : 4651
% 10.15/3.74  #Fact    : 0
% 10.15/3.74  #Define  : 0
% 10.15/3.74  #Split   : 71
% 10.15/3.74  #Chain   : 0
% 10.15/3.74  #Close   : 0
% 10.15/3.74  
% 10.15/3.74  Ordering : KBO
% 10.15/3.74  
% 10.15/3.74  Simplification rules
% 10.15/3.74  ----------------------
% 10.15/3.74  #Subsume      : 1253
% 10.15/3.74  #Demod        : 5494
% 10.15/3.74  #Tautology    : 2371
% 10.15/3.74  #SimpNegUnit  : 170
% 10.15/3.74  #BackRed      : 425
% 10.15/3.74  
% 10.15/3.74  #Partial instantiations: 0
% 10.15/3.74  #Strategies tried      : 1
% 10.15/3.74  
% 10.15/3.74  Timing (in seconds)
% 10.15/3.74  ----------------------
% 10.15/3.74  Preprocessing        : 0.37
% 10.15/3.74  Parsing              : 0.20
% 10.15/3.74  CNF conversion       : 0.03
% 10.15/3.74  Main loop            : 2.50
% 10.15/3.74  Inferencing          : 0.74
% 10.15/3.74  Reduction            : 0.92
% 10.15/3.74  Demodulation         : 0.65
% 10.15/3.74  BG Simplification    : 0.08
% 10.15/3.74  Subsumption          : 0.57
% 10.15/3.74  Abstraction          : 0.10
% 10.15/3.74  MUC search           : 0.00
% 10.15/3.74  Cooper               : 0.00
% 10.15/3.74  Total                : 2.94
% 10.15/3.74  Index Insertion      : 0.00
% 10.15/3.74  Index Deletion       : 0.00
% 10.15/3.75  Index Matching       : 0.00
% 10.15/3.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
