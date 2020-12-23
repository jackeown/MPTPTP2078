%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:53 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 138 expanded)
%              Number of leaves         :   39 (  67 expanded)
%              Depth                    :    9
%              Number of atoms          :  113 ( 296 expanded)
%              Number of equality atoms :   32 (  71 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
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

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_103,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_111,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_103])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_793,plain,(
    ! [B_208,A_209] :
      ( m1_subset_1(B_208,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_208),A_209)))
      | ~ r1_tarski(k2_relat_1(B_208),A_209)
      | ~ v1_funct_1(B_208)
      | ~ v1_relat_1(B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( k7_relset_1(A_45,B_46,C_47,D_48) = k9_relat_1(C_47,D_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1291,plain,(
    ! [B_294,A_295,D_296] :
      ( k7_relset_1(k1_relat_1(B_294),A_295,B_294,D_296) = k9_relat_1(B_294,D_296)
      | ~ r1_tarski(k2_relat_1(B_294),A_295)
      | ~ v1_funct_1(B_294)
      | ~ v1_relat_1(B_294) ) ),
    inference(resolution,[status(thm)],[c_793,c_34])).

tff(c_1300,plain,(
    ! [B_297,D_298] :
      ( k7_relset_1(k1_relat_1(B_297),k2_relat_1(B_297),B_297,D_298) = k9_relat_1(B_297,D_298)
      | ~ v1_funct_1(B_297)
      | ~ v1_relat_1(B_297) ) ),
    inference(resolution,[status(thm)],[c_6,c_1291])).

tff(c_638,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( m1_subset_1(k7_relset_1(A_175,B_176,C_177,D_178),k1_zfmisc_1(B_176))
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_652,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( r1_tarski(k7_relset_1(A_175,B_176,C_177,D_178),B_176)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(resolution,[status(thm)],[c_638,c_22])).

tff(c_817,plain,(
    ! [B_208,A_209,D_178] :
      ( r1_tarski(k7_relset_1(k1_relat_1(B_208),A_209,B_208,D_178),A_209)
      | ~ r1_tarski(k2_relat_1(B_208),A_209)
      | ~ v1_funct_1(B_208)
      | ~ v1_relat_1(B_208) ) ),
    inference(resolution,[status(thm)],[c_793,c_652])).

tff(c_1306,plain,(
    ! [B_297,D_298] :
      ( r1_tarski(k9_relat_1(B_297,D_298),k2_relat_1(B_297))
      | ~ r1_tarski(k2_relat_1(B_297),k2_relat_1(B_297))
      | ~ v1_funct_1(B_297)
      | ~ v1_relat_1(B_297)
      | ~ v1_funct_1(B_297)
      | ~ v1_relat_1(B_297) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1300,c_817])).

tff(c_1320,plain,(
    ! [B_299,D_300] :
      ( r1_tarski(k9_relat_1(B_299,D_300),k2_relat_1(B_299))
      | ~ v1_funct_1(B_299)
      | ~ v1_relat_1(B_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1306])).

tff(c_194,plain,(
    ! [B_96,A_97] :
      ( k1_tarski(k1_funct_1(B_96,A_97)) = k2_relat_1(B_96)
      | k1_tarski(A_97) != k1_relat_1(B_96)
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_200,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_54])).

tff(c_206,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_62,c_200])).

tff(c_208,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_60,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_144,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_relset_1(A_79,B_80,C_81) = k1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_152,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_144])).

tff(c_571,plain,(
    ! [B_172,A_173,C_174] :
      ( k1_xboole_0 = B_172
      | k1_relset_1(A_173,B_172,C_174) = A_173
      | ~ v1_funct_2(C_174,A_173,B_172)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_173,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_581,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_571])).

tff(c_590,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_152,c_581])).

tff(c_592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_56,c_590])).

tff(c_594,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_599,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_58])).

tff(c_688,plain,(
    ! [A_188,B_189,C_190,D_191] :
      ( k7_relset_1(A_188,B_189,C_190,D_191) = k9_relat_1(C_190,D_191)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_698,plain,(
    ! [D_191] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_191) = k9_relat_1('#skF_4',D_191) ),
    inference(resolution,[status(thm)],[c_599,c_688])).

tff(c_593,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_637,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_593])).

tff(c_702,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_637])).

tff(c_1323,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1320,c_702])).

tff(c_1329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_62,c_1323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:41:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.66  
% 3.75/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.66  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.75/1.66  
% 3.75/1.66  %Foreground sorts:
% 3.75/1.66  
% 3.75/1.66  
% 3.75/1.66  %Background operators:
% 3.75/1.66  
% 3.75/1.66  
% 3.75/1.66  %Foreground operators:
% 3.75/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.75/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.75/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.75/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.75/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.75/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.75/1.66  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.75/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.75/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.75/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.75/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.75/1.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.75/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.75/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.75/1.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.75/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.75/1.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.75/1.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.75/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.75/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.75/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.75/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.75/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.75/1.66  
% 3.75/1.67  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.75/1.67  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.75/1.67  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.75/1.67  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 3.75/1.67  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.75/1.67  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.75/1.67  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.75/1.67  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.75/1.67  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.75/1.67  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.75/1.67  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.75/1.67  tff(c_103, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.75/1.67  tff(c_111, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_103])).
% 3.75/1.67  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.75/1.67  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.75/1.67  tff(c_793, plain, (![B_208, A_209]: (m1_subset_1(B_208, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_208), A_209))) | ~r1_tarski(k2_relat_1(B_208), A_209) | ~v1_funct_1(B_208) | ~v1_relat_1(B_208))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.75/1.67  tff(c_34, plain, (![A_45, B_46, C_47, D_48]: (k7_relset_1(A_45, B_46, C_47, D_48)=k9_relat_1(C_47, D_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.75/1.67  tff(c_1291, plain, (![B_294, A_295, D_296]: (k7_relset_1(k1_relat_1(B_294), A_295, B_294, D_296)=k9_relat_1(B_294, D_296) | ~r1_tarski(k2_relat_1(B_294), A_295) | ~v1_funct_1(B_294) | ~v1_relat_1(B_294))), inference(resolution, [status(thm)], [c_793, c_34])).
% 3.75/1.67  tff(c_1300, plain, (![B_297, D_298]: (k7_relset_1(k1_relat_1(B_297), k2_relat_1(B_297), B_297, D_298)=k9_relat_1(B_297, D_298) | ~v1_funct_1(B_297) | ~v1_relat_1(B_297))), inference(resolution, [status(thm)], [c_6, c_1291])).
% 3.75/1.67  tff(c_638, plain, (![A_175, B_176, C_177, D_178]: (m1_subset_1(k7_relset_1(A_175, B_176, C_177, D_178), k1_zfmisc_1(B_176)) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.75/1.67  tff(c_22, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.75/1.67  tff(c_652, plain, (![A_175, B_176, C_177, D_178]: (r1_tarski(k7_relset_1(A_175, B_176, C_177, D_178), B_176) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(resolution, [status(thm)], [c_638, c_22])).
% 3.75/1.67  tff(c_817, plain, (![B_208, A_209, D_178]: (r1_tarski(k7_relset_1(k1_relat_1(B_208), A_209, B_208, D_178), A_209) | ~r1_tarski(k2_relat_1(B_208), A_209) | ~v1_funct_1(B_208) | ~v1_relat_1(B_208))), inference(resolution, [status(thm)], [c_793, c_652])).
% 3.75/1.67  tff(c_1306, plain, (![B_297, D_298]: (r1_tarski(k9_relat_1(B_297, D_298), k2_relat_1(B_297)) | ~r1_tarski(k2_relat_1(B_297), k2_relat_1(B_297)) | ~v1_funct_1(B_297) | ~v1_relat_1(B_297) | ~v1_funct_1(B_297) | ~v1_relat_1(B_297))), inference(superposition, [status(thm), theory('equality')], [c_1300, c_817])).
% 3.75/1.67  tff(c_1320, plain, (![B_299, D_300]: (r1_tarski(k9_relat_1(B_299, D_300), k2_relat_1(B_299)) | ~v1_funct_1(B_299) | ~v1_relat_1(B_299))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1306])).
% 3.75/1.67  tff(c_194, plain, (![B_96, A_97]: (k1_tarski(k1_funct_1(B_96, A_97))=k2_relat_1(B_96) | k1_tarski(A_97)!=k1_relat_1(B_96) | ~v1_funct_1(B_96) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.75/1.67  tff(c_54, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.75/1.67  tff(c_200, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_194, c_54])).
% 3.75/1.67  tff(c_206, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_62, c_200])).
% 3.75/1.67  tff(c_208, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_206])).
% 3.75/1.67  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.75/1.67  tff(c_60, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.75/1.67  tff(c_144, plain, (![A_79, B_80, C_81]: (k1_relset_1(A_79, B_80, C_81)=k1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.75/1.67  tff(c_152, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_144])).
% 3.75/1.67  tff(c_571, plain, (![B_172, A_173, C_174]: (k1_xboole_0=B_172 | k1_relset_1(A_173, B_172, C_174)=A_173 | ~v1_funct_2(C_174, A_173, B_172) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_173, B_172))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.75/1.67  tff(c_581, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_58, c_571])).
% 3.75/1.67  tff(c_590, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_152, c_581])).
% 3.75/1.67  tff(c_592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_56, c_590])).
% 3.75/1.67  tff(c_594, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_206])).
% 3.75/1.67  tff(c_599, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_594, c_58])).
% 3.75/1.67  tff(c_688, plain, (![A_188, B_189, C_190, D_191]: (k7_relset_1(A_188, B_189, C_190, D_191)=k9_relat_1(C_190, D_191) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.75/1.67  tff(c_698, plain, (![D_191]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_191)=k9_relat_1('#skF_4', D_191))), inference(resolution, [status(thm)], [c_599, c_688])).
% 3.75/1.67  tff(c_593, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_206])).
% 3.75/1.67  tff(c_637, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_594, c_593])).
% 3.75/1.67  tff(c_702, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_698, c_637])).
% 3.75/1.67  tff(c_1323, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1320, c_702])).
% 3.75/1.67  tff(c_1329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_62, c_1323])).
% 3.75/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.67  
% 3.75/1.67  Inference rules
% 3.75/1.67  ----------------------
% 3.75/1.67  #Ref     : 0
% 3.75/1.67  #Sup     : 260
% 3.75/1.67  #Fact    : 0
% 3.75/1.67  #Define  : 0
% 3.75/1.67  #Split   : 2
% 3.75/1.67  #Chain   : 0
% 3.75/1.67  #Close   : 0
% 3.75/1.67  
% 3.75/1.67  Ordering : KBO
% 3.75/1.67  
% 3.75/1.67  Simplification rules
% 3.75/1.68  ----------------------
% 3.75/1.68  #Subsume      : 19
% 3.75/1.68  #Demod        : 80
% 3.75/1.68  #Tautology    : 80
% 3.75/1.68  #SimpNegUnit  : 6
% 3.75/1.68  #BackRed      : 11
% 3.75/1.68  
% 3.75/1.68  #Partial instantiations: 0
% 3.75/1.68  #Strategies tried      : 1
% 3.75/1.68  
% 3.75/1.68  Timing (in seconds)
% 3.75/1.68  ----------------------
% 3.75/1.68  Preprocessing        : 0.37
% 3.75/1.68  Parsing              : 0.20
% 3.75/1.68  CNF conversion       : 0.02
% 3.75/1.68  Main loop            : 0.50
% 3.75/1.68  Inferencing          : 0.20
% 3.75/1.68  Reduction            : 0.14
% 3.75/1.68  Demodulation         : 0.10
% 3.75/1.68  BG Simplification    : 0.03
% 3.75/1.68  Subsumption          : 0.09
% 3.75/1.68  Abstraction          : 0.03
% 3.75/1.68  MUC search           : 0.00
% 3.75/1.68  Cooper               : 0.00
% 3.75/1.68  Total                : 0.90
% 3.75/1.68  Index Insertion      : 0.00
% 3.75/1.68  Index Deletion       : 0.00
% 3.75/1.68  Index Matching       : 0.00
% 3.75/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
