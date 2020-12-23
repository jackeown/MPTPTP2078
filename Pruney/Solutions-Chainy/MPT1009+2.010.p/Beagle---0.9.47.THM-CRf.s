%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:43 EST 2020

% Result     : Theorem 5.57s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 281 expanded)
%              Number of leaves         :   41 ( 113 expanded)
%              Depth                    :   13
%              Number of atoms          :  133 ( 606 expanded)
%              Number of equality atoms :   47 ( 181 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_82,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_192,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_205,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_192])).

tff(c_44,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k9_relat_1(B_22,A_21),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_48,plain,(
    ! [B_25,A_24] :
      ( k1_tarski(k1_funct_1(B_25,A_24)) = k2_relat_1(B_25)
      | k1_tarski(A_24) != k1_relat_1(B_25)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_593,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( k7_relset_1(A_119,B_120,C_121,D_122) = k9_relat_1(C_121,D_122)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_604,plain,(
    ! [D_122] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_122) = k9_relat_1('#skF_4',D_122) ),
    inference(resolution,[status(thm)],[c_64,c_593])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_636,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_60])).

tff(c_648,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_636])).

tff(c_650,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_68,c_648])).

tff(c_759,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_650])).

tff(c_347,plain,(
    ! [C_93,A_94,B_95] :
      ( v4_relat_1(C_93,A_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_362,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_347])).

tff(c_38,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_853,plain,(
    ! [B_155,C_156,A_157] :
      ( k2_tarski(B_155,C_156) = A_157
      | k1_tarski(C_156) = A_157
      | k1_tarski(B_155) = A_157
      | k1_xboole_0 = A_157
      | ~ r1_tarski(A_157,k2_tarski(B_155,C_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_870,plain,(
    ! [A_4,A_157] :
      ( k2_tarski(A_4,A_4) = A_157
      | k1_tarski(A_4) = A_157
      | k1_tarski(A_4) = A_157
      | k1_xboole_0 = A_157
      | ~ r1_tarski(A_157,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_853])).

tff(c_3482,plain,(
    ! [A_311,A_312] :
      ( k1_tarski(A_311) = A_312
      | k1_tarski(A_311) = A_312
      | k1_tarski(A_311) = A_312
      | k1_xboole_0 = A_312
      | ~ r1_tarski(A_312,k1_tarski(A_311)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_870])).

tff(c_4203,plain,(
    ! [A_331,B_332] :
      ( k1_tarski(A_331) = k1_relat_1(B_332)
      | k1_relat_1(B_332) = k1_xboole_0
      | ~ v4_relat_1(B_332,k1_tarski(A_331))
      | ~ v1_relat_1(B_332) ) ),
    inference(resolution,[status(thm)],[c_38,c_3482])).

tff(c_4265,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_362,c_4203])).

tff(c_4298,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_4265])).

tff(c_4299,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_759,c_4298])).

tff(c_30,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_727,plain,(
    ! [C_139,A_140,B_141] :
      ( m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ r1_tarski(k2_relat_1(C_139),B_141)
      | ~ r1_tarski(k1_relat_1(C_139),A_140)
      | ~ v1_relat_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4086,plain,(
    ! [C_325,A_326,B_327] :
      ( r1_tarski(C_325,k2_zfmisc_1(A_326,B_327))
      | ~ r1_tarski(k2_relat_1(C_325),B_327)
      | ~ r1_tarski(k1_relat_1(C_325),A_326)
      | ~ v1_relat_1(C_325) ) ),
    inference(resolution,[status(thm)],[c_727,c_32])).

tff(c_4114,plain,(
    ! [C_328,A_329] :
      ( r1_tarski(C_328,k2_zfmisc_1(A_329,k2_relat_1(C_328)))
      | ~ r1_tarski(k1_relat_1(C_328),A_329)
      | ~ v1_relat_1(C_328) ) ),
    inference(resolution,[status(thm)],[c_6,c_4086])).

tff(c_4157,plain,(
    ! [C_328] :
      ( r1_tarski(C_328,k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_328),k1_xboole_0)
      | ~ v1_relat_1(C_328) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_4114])).

tff(c_4304,plain,
    ( r1_tarski('#skF_4',k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4299,c_4157])).

tff(c_4359,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_8,c_4304])).

tff(c_157,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_178,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_157])).

tff(c_4428,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4359,c_178])).

tff(c_4505,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4428,c_8])).

tff(c_46,plain,(
    ! [A_23] : k9_relat_1(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4502,plain,(
    ! [A_23] : k9_relat_1('#skF_4',A_23) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4428,c_4428,c_46])).

tff(c_4923,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4502,c_636])).

tff(c_4927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4505,c_4923])).

tff(c_4928,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_650])).

tff(c_4966,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_4928])).

tff(c_4970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_4966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:11:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.57/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.57/2.16  
% 5.57/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.57/2.16  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.57/2.16  
% 5.57/2.16  %Foreground sorts:
% 5.57/2.16  
% 5.57/2.16  
% 5.57/2.16  %Background operators:
% 5.57/2.16  
% 5.57/2.16  
% 5.57/2.16  %Foreground operators:
% 5.57/2.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.57/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.57/2.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.57/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.57/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.57/2.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.57/2.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.57/2.16  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.57/2.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.57/2.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.57/2.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.57/2.16  tff('#skF_2', type, '#skF_2': $i).
% 5.57/2.16  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.57/2.16  tff('#skF_3', type, '#skF_3': $i).
% 5.57/2.16  tff('#skF_1', type, '#skF_1': $i).
% 5.57/2.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.57/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.57/2.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.57/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.57/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.57/2.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.57/2.16  tff('#skF_4', type, '#skF_4': $i).
% 5.57/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.57/2.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.57/2.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.57/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.57/2.16  
% 5.78/2.18  tff(f_124, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 5.78/2.18  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.78/2.18  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 5.78/2.18  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.78/2.18  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 5.78/2.18  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.78/2.18  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.78/2.18  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.78/2.18  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.78/2.18  tff(f_54, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 5.78/2.18  tff(f_60, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.78/2.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.78/2.18  tff(f_112, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.78/2.18  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.78/2.18  tff(f_82, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 5.78/2.18  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.78/2.18  tff(c_192, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.78/2.18  tff(c_205, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_192])).
% 5.78/2.18  tff(c_44, plain, (![B_22, A_21]: (r1_tarski(k9_relat_1(B_22, A_21), k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.78/2.18  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.78/2.18  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.78/2.18  tff(c_48, plain, (![B_25, A_24]: (k1_tarski(k1_funct_1(B_25, A_24))=k2_relat_1(B_25) | k1_tarski(A_24)!=k1_relat_1(B_25) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.78/2.18  tff(c_593, plain, (![A_119, B_120, C_121, D_122]: (k7_relset_1(A_119, B_120, C_121, D_122)=k9_relat_1(C_121, D_122) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.78/2.18  tff(c_604, plain, (![D_122]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_122)=k9_relat_1('#skF_4', D_122))), inference(resolution, [status(thm)], [c_64, c_593])).
% 5.78/2.18  tff(c_60, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.78/2.18  tff(c_636, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_604, c_60])).
% 5.78/2.18  tff(c_648, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_636])).
% 5.78/2.18  tff(c_650, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_68, c_648])).
% 5.78/2.18  tff(c_759, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_650])).
% 5.78/2.18  tff(c_347, plain, (![C_93, A_94, B_95]: (v4_relat_1(C_93, A_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.78/2.18  tff(c_362, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_347])).
% 5.78/2.18  tff(c_38, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.78/2.18  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.78/2.18  tff(c_853, plain, (![B_155, C_156, A_157]: (k2_tarski(B_155, C_156)=A_157 | k1_tarski(C_156)=A_157 | k1_tarski(B_155)=A_157 | k1_xboole_0=A_157 | ~r1_tarski(A_157, k2_tarski(B_155, C_156)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.78/2.18  tff(c_870, plain, (![A_4, A_157]: (k2_tarski(A_4, A_4)=A_157 | k1_tarski(A_4)=A_157 | k1_tarski(A_4)=A_157 | k1_xboole_0=A_157 | ~r1_tarski(A_157, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_853])).
% 5.78/2.18  tff(c_3482, plain, (![A_311, A_312]: (k1_tarski(A_311)=A_312 | k1_tarski(A_311)=A_312 | k1_tarski(A_311)=A_312 | k1_xboole_0=A_312 | ~r1_tarski(A_312, k1_tarski(A_311)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_870])).
% 5.78/2.18  tff(c_4203, plain, (![A_331, B_332]: (k1_tarski(A_331)=k1_relat_1(B_332) | k1_relat_1(B_332)=k1_xboole_0 | ~v4_relat_1(B_332, k1_tarski(A_331)) | ~v1_relat_1(B_332))), inference(resolution, [status(thm)], [c_38, c_3482])).
% 5.78/2.18  tff(c_4265, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_362, c_4203])).
% 5.78/2.18  tff(c_4298, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_205, c_4265])).
% 5.78/2.18  tff(c_4299, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_759, c_4298])).
% 5.78/2.18  tff(c_30, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.78/2.18  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.78/2.18  tff(c_727, plain, (![C_139, A_140, B_141]: (m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~r1_tarski(k2_relat_1(C_139), B_141) | ~r1_tarski(k1_relat_1(C_139), A_140) | ~v1_relat_1(C_139))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.78/2.18  tff(c_32, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.78/2.18  tff(c_4086, plain, (![C_325, A_326, B_327]: (r1_tarski(C_325, k2_zfmisc_1(A_326, B_327)) | ~r1_tarski(k2_relat_1(C_325), B_327) | ~r1_tarski(k1_relat_1(C_325), A_326) | ~v1_relat_1(C_325))), inference(resolution, [status(thm)], [c_727, c_32])).
% 5.78/2.18  tff(c_4114, plain, (![C_328, A_329]: (r1_tarski(C_328, k2_zfmisc_1(A_329, k2_relat_1(C_328))) | ~r1_tarski(k1_relat_1(C_328), A_329) | ~v1_relat_1(C_328))), inference(resolution, [status(thm)], [c_6, c_4086])).
% 5.78/2.18  tff(c_4157, plain, (![C_328]: (r1_tarski(C_328, k1_xboole_0) | ~r1_tarski(k1_relat_1(C_328), k1_xboole_0) | ~v1_relat_1(C_328))), inference(superposition, [status(thm), theory('equality')], [c_30, c_4114])).
% 5.78/2.18  tff(c_4304, plain, (r1_tarski('#skF_4', k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4299, c_4157])).
% 5.78/2.18  tff(c_4359, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_205, c_8, c_4304])).
% 5.78/2.18  tff(c_157, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.78/2.18  tff(c_178, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_157])).
% 5.78/2.18  tff(c_4428, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4359, c_178])).
% 5.78/2.18  tff(c_4505, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4428, c_8])).
% 5.78/2.18  tff(c_46, plain, (![A_23]: (k9_relat_1(k1_xboole_0, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.78/2.18  tff(c_4502, plain, (![A_23]: (k9_relat_1('#skF_4', A_23)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4428, c_4428, c_46])).
% 5.78/2.18  tff(c_4923, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4502, c_636])).
% 5.78/2.18  tff(c_4927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4505, c_4923])).
% 5.78/2.18  tff(c_4928, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_650])).
% 5.78/2.18  tff(c_4966, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_4928])).
% 5.78/2.18  tff(c_4970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_4966])).
% 5.78/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.18  
% 5.78/2.18  Inference rules
% 5.78/2.18  ----------------------
% 5.78/2.18  #Ref     : 0
% 5.78/2.18  #Sup     : 1025
% 5.78/2.18  #Fact    : 0
% 5.78/2.18  #Define  : 0
% 5.78/2.18  #Split   : 2
% 5.78/2.18  #Chain   : 0
% 5.78/2.18  #Close   : 0
% 5.78/2.18  
% 5.78/2.18  Ordering : KBO
% 5.78/2.18  
% 5.78/2.18  Simplification rules
% 5.78/2.18  ----------------------
% 5.78/2.18  #Subsume      : 107
% 5.78/2.18  #Demod        : 1837
% 5.78/2.18  #Tautology    : 540
% 5.78/2.18  #SimpNegUnit  : 1
% 5.78/2.18  #BackRed      : 85
% 5.78/2.18  
% 5.78/2.18  #Partial instantiations: 0
% 5.78/2.18  #Strategies tried      : 1
% 5.78/2.18  
% 5.78/2.18  Timing (in seconds)
% 5.78/2.18  ----------------------
% 5.78/2.18  Preprocessing        : 0.33
% 5.78/2.18  Parsing              : 0.18
% 5.78/2.18  CNF conversion       : 0.02
% 5.78/2.18  Main loop            : 1.07
% 5.78/2.18  Inferencing          : 0.33
% 5.78/2.18  Reduction            : 0.42
% 5.78/2.18  Demodulation         : 0.33
% 5.78/2.18  BG Simplification    : 0.04
% 5.78/2.18  Subsumption          : 0.21
% 5.78/2.18  Abstraction          : 0.04
% 5.78/2.18  MUC search           : 0.00
% 5.78/2.18  Cooper               : 0.00
% 5.78/2.18  Total                : 1.44
% 5.78/2.18  Index Insertion      : 0.00
% 5.78/2.18  Index Deletion       : 0.00
% 5.78/2.18  Index Matching       : 0.00
% 5.78/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
