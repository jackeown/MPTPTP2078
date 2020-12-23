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
% DateTime   : Thu Dec  3 10:18:04 EST 2020

% Result     : Theorem 4.84s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 118 expanded)
%              Number of leaves         :   35 (  59 expanded)
%              Depth                    :    7
%              Number of atoms          :  114 ( 270 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_16,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_90,plain,(
    ! [B_75,A_76] :
      ( v1_relat_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_52,c_90])).

tff(c_101,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_97])).

tff(c_56,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    ! [A_12,B_35,D_50] :
      ( k1_funct_1(A_12,'#skF_5'(A_12,B_35,k9_relat_1(A_12,B_35),D_50)) = D_50
      | ~ r2_hidden(D_50,k9_relat_1(A_12,B_35))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_69,plain,(
    ! [B_69,A_70] :
      ( m1_subset_1(B_69,A_70)
      | ~ v1_xboole_0(B_69)
      | ~ v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_48,plain,(
    ! [E_62] :
      ( k1_funct_1('#skF_9',E_62) != '#skF_6'
      | ~ m1_subset_1(E_62,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_74,plain,(
    ! [B_69] :
      ( k1_funct_1('#skF_9',B_69) != '#skF_6'
      | ~ v1_xboole_0(B_69)
      | ~ v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_69,c_48])).

tff(c_137,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_224,plain,(
    ! [A_106,B_107,D_108] :
      ( r2_hidden('#skF_5'(A_106,B_107,k9_relat_1(A_106,B_107),D_108),B_107)
      | ~ r2_hidden(D_108,k9_relat_1(A_106,B_107))
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_908,plain,(
    ! [A_231,B_232,D_233] :
      ( m1_subset_1('#skF_5'(A_231,B_232,k9_relat_1(A_231,B_232),D_233),B_232)
      | v1_xboole_0(B_232)
      | ~ r2_hidden(D_233,k9_relat_1(A_231,B_232))
      | ~ v1_funct_1(A_231)
      | ~ v1_relat_1(A_231) ) ),
    inference(resolution,[status(thm)],[c_224,c_6])).

tff(c_928,plain,(
    ! [A_231,D_233] :
      ( k1_funct_1('#skF_9','#skF_5'(A_231,'#skF_7',k9_relat_1(A_231,'#skF_7'),D_233)) != '#skF_6'
      | v1_xboole_0('#skF_7')
      | ~ r2_hidden(D_233,k9_relat_1(A_231,'#skF_7'))
      | ~ v1_funct_1(A_231)
      | ~ v1_relat_1(A_231) ) ),
    inference(resolution,[status(thm)],[c_908,c_48])).

tff(c_937,plain,(
    ! [A_234,D_235] :
      ( k1_funct_1('#skF_9','#skF_5'(A_234,'#skF_7',k9_relat_1(A_234,'#skF_7'),D_235)) != '#skF_6'
      | ~ r2_hidden(D_235,k9_relat_1(A_234,'#skF_7'))
      | ~ v1_funct_1(A_234)
      | ~ v1_relat_1(A_234) ) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_928])).

tff(c_941,plain,(
    ! [D_50] :
      ( D_50 != '#skF_6'
      | ~ r2_hidden(D_50,k9_relat_1('#skF_9','#skF_7'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_50,k9_relat_1('#skF_9','#skF_7'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_937])).

tff(c_944,plain,(
    ~ r2_hidden('#skF_6',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_56,c_101,c_56,c_941])).

tff(c_140,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( k7_relset_1(A_81,B_82,C_83,D_84) = k9_relat_1(C_83,D_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_151,plain,(
    ! [D_84] : k7_relset_1('#skF_7','#skF_8','#skF_9',D_84) = k9_relat_1('#skF_9',D_84) ),
    inference(resolution,[status(thm)],[c_52,c_140])).

tff(c_178,plain,(
    ! [A_90,B_91,C_92] :
      ( k7_relset_1(A_90,B_91,C_92,A_90) = k2_relset_1(A_90,B_91,C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_186,plain,(
    k7_relset_1('#skF_7','#skF_8','#skF_9','#skF_7') = k2_relset_1('#skF_7','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_178])).

tff(c_190,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k9_relat_1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_186])).

tff(c_50,plain,(
    r2_hidden('#skF_6',k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_193,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_50])).

tff(c_946,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_944,c_193])).

tff(c_948,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_955,plain,(
    ! [A_237,B_238,C_239,D_240] :
      ( k7_relset_1(A_237,B_238,C_239,D_240) = k9_relat_1(C_239,D_240)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_966,plain,(
    ! [D_240] : k7_relset_1('#skF_7','#skF_8','#skF_9',D_240) = k9_relat_1('#skF_9',D_240) ),
    inference(resolution,[status(thm)],[c_52,c_955])).

tff(c_994,plain,(
    ! [A_247,B_248,C_249] :
      ( k7_relset_1(A_247,B_248,C_249,A_247) = k2_relset_1(A_247,B_248,C_249)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1002,plain,(
    k7_relset_1('#skF_7','#skF_8','#skF_9','#skF_7') = k2_relset_1('#skF_7','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_994])).

tff(c_1006,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k9_relat_1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_966,c_1002])).

tff(c_1009,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1006,c_50])).

tff(c_1042,plain,(
    ! [A_260,B_261,D_262] :
      ( r2_hidden('#skF_5'(A_260,B_261,k9_relat_1(A_260,B_261),D_262),B_261)
      | ~ r2_hidden(D_262,k9_relat_1(A_260,B_261))
      | ~ v1_funct_1(A_260)
      | ~ v1_relat_1(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1051,plain,(
    ! [B_263,D_264,A_265] :
      ( ~ v1_xboole_0(B_263)
      | ~ r2_hidden(D_264,k9_relat_1(A_265,B_263))
      | ~ v1_funct_1(A_265)
      | ~ v1_relat_1(A_265) ) ),
    inference(resolution,[status(thm)],[c_1042,c_2])).

tff(c_1058,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1009,c_1051])).

tff(c_1074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_56,c_948,c_1058])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:33:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.84/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/2.18  
% 4.84/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/2.18  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 4.84/2.18  
% 4.84/2.18  %Foreground sorts:
% 4.84/2.18  
% 4.84/2.18  
% 4.84/2.18  %Background operators:
% 4.84/2.18  
% 4.84/2.18  
% 4.84/2.18  %Foreground operators:
% 4.84/2.18  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.84/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.84/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.84/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.84/2.18  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.84/2.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.84/2.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.84/2.18  tff('#skF_7', type, '#skF_7': $i).
% 4.84/2.18  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.84/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.84/2.18  tff('#skF_6', type, '#skF_6': $i).
% 4.84/2.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.84/2.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.84/2.18  tff('#skF_9', type, '#skF_9': $i).
% 4.84/2.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.84/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.84/2.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.84/2.18  tff('#skF_8', type, '#skF_8': $i).
% 4.84/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.84/2.18  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.84/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.84/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.84/2.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.84/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.84/2.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.84/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.84/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.84/2.18  
% 4.84/2.19  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.84/2.19  tff(f_96, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 4.84/2.19  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.84/2.19  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 4.84/2.19  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.84/2.19  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.84/2.19  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 4.84/2.19  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.84/2.19  tff(c_16, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.84/2.19  tff(c_52, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.84/2.19  tff(c_90, plain, (![B_75, A_76]: (v1_relat_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.84/2.19  tff(c_97, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_52, c_90])).
% 4.84/2.19  tff(c_101, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_97])).
% 4.84/2.19  tff(c_56, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.84/2.19  tff(c_20, plain, (![A_12, B_35, D_50]: (k1_funct_1(A_12, '#skF_5'(A_12, B_35, k9_relat_1(A_12, B_35), D_50))=D_50 | ~r2_hidden(D_50, k9_relat_1(A_12, B_35)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.84/2.19  tff(c_69, plain, (![B_69, A_70]: (m1_subset_1(B_69, A_70) | ~v1_xboole_0(B_69) | ~v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.84/2.19  tff(c_48, plain, (![E_62]: (k1_funct_1('#skF_9', E_62)!='#skF_6' | ~m1_subset_1(E_62, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.84/2.19  tff(c_74, plain, (![B_69]: (k1_funct_1('#skF_9', B_69)!='#skF_6' | ~v1_xboole_0(B_69) | ~v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_69, c_48])).
% 4.84/2.19  tff(c_137, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_74])).
% 4.84/2.19  tff(c_224, plain, (![A_106, B_107, D_108]: (r2_hidden('#skF_5'(A_106, B_107, k9_relat_1(A_106, B_107), D_108), B_107) | ~r2_hidden(D_108, k9_relat_1(A_106, B_107)) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.84/2.19  tff(c_6, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.84/2.19  tff(c_908, plain, (![A_231, B_232, D_233]: (m1_subset_1('#skF_5'(A_231, B_232, k9_relat_1(A_231, B_232), D_233), B_232) | v1_xboole_0(B_232) | ~r2_hidden(D_233, k9_relat_1(A_231, B_232)) | ~v1_funct_1(A_231) | ~v1_relat_1(A_231))), inference(resolution, [status(thm)], [c_224, c_6])).
% 4.84/2.19  tff(c_928, plain, (![A_231, D_233]: (k1_funct_1('#skF_9', '#skF_5'(A_231, '#skF_7', k9_relat_1(A_231, '#skF_7'), D_233))!='#skF_6' | v1_xboole_0('#skF_7') | ~r2_hidden(D_233, k9_relat_1(A_231, '#skF_7')) | ~v1_funct_1(A_231) | ~v1_relat_1(A_231))), inference(resolution, [status(thm)], [c_908, c_48])).
% 4.84/2.19  tff(c_937, plain, (![A_234, D_235]: (k1_funct_1('#skF_9', '#skF_5'(A_234, '#skF_7', k9_relat_1(A_234, '#skF_7'), D_235))!='#skF_6' | ~r2_hidden(D_235, k9_relat_1(A_234, '#skF_7')) | ~v1_funct_1(A_234) | ~v1_relat_1(A_234))), inference(negUnitSimplification, [status(thm)], [c_137, c_928])).
% 4.84/2.19  tff(c_941, plain, (![D_50]: (D_50!='#skF_6' | ~r2_hidden(D_50, k9_relat_1('#skF_9', '#skF_7')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_50, k9_relat_1('#skF_9', '#skF_7')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_937])).
% 4.84/2.19  tff(c_944, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_56, c_101, c_56, c_941])).
% 4.84/2.19  tff(c_140, plain, (![A_81, B_82, C_83, D_84]: (k7_relset_1(A_81, B_82, C_83, D_84)=k9_relat_1(C_83, D_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.84/2.19  tff(c_151, plain, (![D_84]: (k7_relset_1('#skF_7', '#skF_8', '#skF_9', D_84)=k9_relat_1('#skF_9', D_84))), inference(resolution, [status(thm)], [c_52, c_140])).
% 4.84/2.19  tff(c_178, plain, (![A_90, B_91, C_92]: (k7_relset_1(A_90, B_91, C_92, A_90)=k2_relset_1(A_90, B_91, C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.84/2.19  tff(c_186, plain, (k7_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_7')=k2_relset_1('#skF_7', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_52, c_178])).
% 4.84/2.19  tff(c_190, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k9_relat_1('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_186])).
% 4.84/2.19  tff(c_50, plain, (r2_hidden('#skF_6', k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.84/2.19  tff(c_193, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_50])).
% 4.84/2.19  tff(c_946, plain, $false, inference(negUnitSimplification, [status(thm)], [c_944, c_193])).
% 4.84/2.19  tff(c_948, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 4.84/2.19  tff(c_955, plain, (![A_237, B_238, C_239, D_240]: (k7_relset_1(A_237, B_238, C_239, D_240)=k9_relat_1(C_239, D_240) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.84/2.19  tff(c_966, plain, (![D_240]: (k7_relset_1('#skF_7', '#skF_8', '#skF_9', D_240)=k9_relat_1('#skF_9', D_240))), inference(resolution, [status(thm)], [c_52, c_955])).
% 4.84/2.19  tff(c_994, plain, (![A_247, B_248, C_249]: (k7_relset_1(A_247, B_248, C_249, A_247)=k2_relset_1(A_247, B_248, C_249) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.84/2.19  tff(c_1002, plain, (k7_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_7')=k2_relset_1('#skF_7', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_52, c_994])).
% 4.84/2.19  tff(c_1006, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k9_relat_1('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_966, c_1002])).
% 4.84/2.19  tff(c_1009, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1006, c_50])).
% 4.84/2.19  tff(c_1042, plain, (![A_260, B_261, D_262]: (r2_hidden('#skF_5'(A_260, B_261, k9_relat_1(A_260, B_261), D_262), B_261) | ~r2_hidden(D_262, k9_relat_1(A_260, B_261)) | ~v1_funct_1(A_260) | ~v1_relat_1(A_260))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.84/2.19  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.84/2.19  tff(c_1051, plain, (![B_263, D_264, A_265]: (~v1_xboole_0(B_263) | ~r2_hidden(D_264, k9_relat_1(A_265, B_263)) | ~v1_funct_1(A_265) | ~v1_relat_1(A_265))), inference(resolution, [status(thm)], [c_1042, c_2])).
% 4.84/2.19  tff(c_1058, plain, (~v1_xboole_0('#skF_7') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1009, c_1051])).
% 4.84/2.19  tff(c_1074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_56, c_948, c_1058])).
% 4.84/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/2.19  
% 4.84/2.19  Inference rules
% 4.84/2.19  ----------------------
% 4.84/2.19  #Ref     : 0
% 4.84/2.19  #Sup     : 228
% 4.84/2.19  #Fact    : 0
% 4.84/2.19  #Define  : 0
% 4.84/2.19  #Split   : 5
% 4.84/2.19  #Chain   : 0
% 4.84/2.19  #Close   : 0
% 4.84/2.19  
% 4.84/2.19  Ordering : KBO
% 4.84/2.19  
% 4.84/2.19  Simplification rules
% 4.84/2.19  ----------------------
% 4.84/2.19  #Subsume      : 33
% 4.84/2.19  #Demod        : 30
% 4.84/2.19  #Tautology    : 27
% 4.84/2.19  #SimpNegUnit  : 8
% 4.84/2.19  #BackRed      : 7
% 4.84/2.19  
% 4.84/2.19  #Partial instantiations: 0
% 4.84/2.19  #Strategies tried      : 1
% 4.84/2.19  
% 4.84/2.19  Timing (in seconds)
% 4.84/2.19  ----------------------
% 4.84/2.20  Preprocessing        : 0.54
% 4.84/2.20  Parsing              : 0.27
% 4.84/2.20  CNF conversion       : 0.05
% 4.84/2.20  Main loop            : 0.84
% 4.84/2.20  Inferencing          : 0.28
% 4.84/2.20  Reduction            : 0.19
% 4.84/2.20  Demodulation         : 0.13
% 4.84/2.20  BG Simplification    : 0.05
% 4.84/2.20  Subsumption          : 0.25
% 4.84/2.20  Abstraction          : 0.06
% 4.84/2.20  MUC search           : 0.00
% 4.84/2.20  Cooper               : 0.00
% 4.84/2.20  Total                : 1.42
% 4.84/2.20  Index Insertion      : 0.00
% 4.84/2.20  Index Deletion       : 0.00
% 4.84/2.20  Index Matching       : 0.00
% 4.84/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
