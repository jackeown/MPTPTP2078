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
% DateTime   : Thu Dec  3 10:17:59 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 165 expanded)
%              Number of leaves         :   40 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 371 expanded)
%              Number of equality atoms :   33 (  96 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_105,plain,(
    ! [C_49,B_50,A_51] :
      ( v5_relat_1(C_49,B_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_114,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_105])).

tff(c_86,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_95,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_86])).

tff(c_145,plain,(
    ! [A_63,B_64,C_65] :
      ( k2_relset_1(A_63,B_64,C_65) = k2_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_154,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_145])).

tff(c_52,plain,(
    r2_hidden('#skF_3',k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_157,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_52])).

tff(c_20,plain,(
    ! [C_17,A_14,B_15] :
      ( r2_hidden(C_17,A_14)
      | ~ r2_hidden(C_17,k2_relat_1(B_15))
      | ~ v5_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_163,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_3',A_14)
      | ~ v5_relat_1('#skF_6',A_14)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_157,c_20])).

tff(c_176,plain,(
    ! [A_66] :
      ( r2_hidden('#skF_3',A_66)
      | ~ v5_relat_1('#skF_6',A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_163])).

tff(c_180,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_176])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_188,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_180,c_2])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_131,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_140,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_131])).

tff(c_874,plain,(
    ! [B_184,A_185,C_186] :
      ( k1_xboole_0 = B_184
      | k1_relset_1(A_185,B_184,C_186) = A_185
      | ~ v1_funct_2(C_186,A_185,B_184)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_185,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_885,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_874])).

tff(c_890,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_140,c_885])).

tff(c_891,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_890])).

tff(c_18,plain,(
    ! [A_13] :
      ( k9_relat_1(A_13,k1_relat_1(A_13)) = k2_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_915,plain,
    ( k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_891,c_18])).

tff(c_931,plain,(
    k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_915])).

tff(c_193,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden('#skF_2'(A_75,B_76,C_77),B_76)
      | ~ r2_hidden(A_75,k9_relat_1(C_77,B_76))
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_204,plain,(
    ! [A_75,B_76,C_77] :
      ( m1_subset_1('#skF_2'(A_75,B_76,C_77),B_76)
      | ~ r2_hidden(A_75,k9_relat_1(C_77,B_76))
      | ~ v1_relat_1(C_77) ) ),
    inference(resolution,[status(thm)],[c_193,c_8])).

tff(c_972,plain,(
    ! [A_75] :
      ( m1_subset_1('#skF_2'(A_75,'#skF_4','#skF_6'),'#skF_4')
      | ~ r2_hidden(A_75,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_204])).

tff(c_1013,plain,(
    ! [A_187] :
      ( m1_subset_1('#skF_2'(A_187,'#skF_4','#skF_6'),'#skF_4')
      | ~ r2_hidden(A_187,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_972])).

tff(c_1041,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_157,c_1013])).

tff(c_50,plain,(
    ! [E_37] :
      ( k1_funct_1('#skF_6',E_37) != '#skF_3'
      | ~ m1_subset_1(E_37,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1048,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1041,c_50])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_651,plain,(
    ! [A_158,B_159,C_160] :
      ( r2_hidden(k4_tarski('#skF_2'(A_158,B_159,C_160),A_158),C_160)
      | ~ r2_hidden(A_158,k9_relat_1(C_160,B_159))
      | ~ v1_relat_1(C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [C_20,A_18,B_19] :
      ( k1_funct_1(C_20,A_18) = B_19
      | ~ r2_hidden(k4_tarski(A_18,B_19),C_20)
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1435,plain,(
    ! [C_223,A_224,B_225] :
      ( k1_funct_1(C_223,'#skF_2'(A_224,B_225,C_223)) = A_224
      | ~ v1_funct_1(C_223)
      | ~ r2_hidden(A_224,k9_relat_1(C_223,B_225))
      | ~ v1_relat_1(C_223) ) ),
    inference(resolution,[status(thm)],[c_651,c_24])).

tff(c_1439,plain,(
    ! [A_224] :
      ( k1_funct_1('#skF_6','#skF_2'(A_224,'#skF_4','#skF_6')) = A_224
      | ~ v1_funct_1('#skF_6')
      | ~ r2_hidden(A_224,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_1435])).

tff(c_1465,plain,(
    ! [A_226] :
      ( k1_funct_1('#skF_6','#skF_2'(A_226,'#skF_4','#skF_6')) = A_226
      | ~ r2_hidden(A_226,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_58,c_1439])).

tff(c_1484,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_157,c_1465])).

tff(c_1496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1048,c_1484])).

tff(c_1497,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_890])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1505,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1497,c_6])).

tff(c_1507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_1505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:40:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.66  
% 3.73/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.66  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.91/1.66  
% 3.91/1.66  %Foreground sorts:
% 3.91/1.66  
% 3.91/1.66  
% 3.91/1.66  %Background operators:
% 3.91/1.66  
% 3.91/1.66  
% 3.91/1.66  %Foreground operators:
% 3.91/1.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.91/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.91/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.91/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.91/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.91/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.91/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.91/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.91/1.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.91/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.91/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.91/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.91/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.91/1.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.91/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.91/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.91/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.91/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.91/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.91/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.91/1.66  
% 3.91/1.68  tff(f_122, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 3.91/1.68  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.91/1.68  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.91/1.68  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.91/1.68  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 3.91/1.68  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.91/1.68  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.91/1.68  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.91/1.68  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.91/1.68  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.91/1.68  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.91/1.68  tff(f_70, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.91/1.68  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.91/1.68  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.91/1.68  tff(c_105, plain, (![C_49, B_50, A_51]: (v5_relat_1(C_49, B_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.91/1.68  tff(c_114, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_105])).
% 3.91/1.68  tff(c_86, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.91/1.68  tff(c_95, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_86])).
% 3.91/1.68  tff(c_145, plain, (![A_63, B_64, C_65]: (k2_relset_1(A_63, B_64, C_65)=k2_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.91/1.68  tff(c_154, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_145])).
% 3.91/1.68  tff(c_52, plain, (r2_hidden('#skF_3', k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.91/1.68  tff(c_157, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_52])).
% 3.91/1.68  tff(c_20, plain, (![C_17, A_14, B_15]: (r2_hidden(C_17, A_14) | ~r2_hidden(C_17, k2_relat_1(B_15)) | ~v5_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.91/1.68  tff(c_163, plain, (![A_14]: (r2_hidden('#skF_3', A_14) | ~v5_relat_1('#skF_6', A_14) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_157, c_20])).
% 3.91/1.68  tff(c_176, plain, (![A_66]: (r2_hidden('#skF_3', A_66) | ~v5_relat_1('#skF_6', A_66))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_163])).
% 3.91/1.68  tff(c_180, plain, (r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_114, c_176])).
% 3.91/1.68  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.68  tff(c_188, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_180, c_2])).
% 3.91/1.68  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.91/1.68  tff(c_131, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.91/1.68  tff(c_140, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_131])).
% 3.91/1.68  tff(c_874, plain, (![B_184, A_185, C_186]: (k1_xboole_0=B_184 | k1_relset_1(A_185, B_184, C_186)=A_185 | ~v1_funct_2(C_186, A_185, B_184) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_185, B_184))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.91/1.68  tff(c_885, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_874])).
% 3.91/1.68  tff(c_890, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_140, c_885])).
% 3.91/1.68  tff(c_891, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_890])).
% 3.91/1.68  tff(c_18, plain, (![A_13]: (k9_relat_1(A_13, k1_relat_1(A_13))=k2_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.91/1.68  tff(c_915, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_891, c_18])).
% 3.91/1.68  tff(c_931, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_915])).
% 3.91/1.68  tff(c_193, plain, (![A_75, B_76, C_77]: (r2_hidden('#skF_2'(A_75, B_76, C_77), B_76) | ~r2_hidden(A_75, k9_relat_1(C_77, B_76)) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.91/1.68  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.91/1.68  tff(c_204, plain, (![A_75, B_76, C_77]: (m1_subset_1('#skF_2'(A_75, B_76, C_77), B_76) | ~r2_hidden(A_75, k9_relat_1(C_77, B_76)) | ~v1_relat_1(C_77))), inference(resolution, [status(thm)], [c_193, c_8])).
% 3.91/1.68  tff(c_972, plain, (![A_75]: (m1_subset_1('#skF_2'(A_75, '#skF_4', '#skF_6'), '#skF_4') | ~r2_hidden(A_75, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_931, c_204])).
% 3.91/1.68  tff(c_1013, plain, (![A_187]: (m1_subset_1('#skF_2'(A_187, '#skF_4', '#skF_6'), '#skF_4') | ~r2_hidden(A_187, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_972])).
% 3.91/1.68  tff(c_1041, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_157, c_1013])).
% 3.91/1.68  tff(c_50, plain, (![E_37]: (k1_funct_1('#skF_6', E_37)!='#skF_3' | ~m1_subset_1(E_37, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.91/1.68  tff(c_1048, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))!='#skF_3'), inference(resolution, [status(thm)], [c_1041, c_50])).
% 3.91/1.68  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.91/1.68  tff(c_651, plain, (![A_158, B_159, C_160]: (r2_hidden(k4_tarski('#skF_2'(A_158, B_159, C_160), A_158), C_160) | ~r2_hidden(A_158, k9_relat_1(C_160, B_159)) | ~v1_relat_1(C_160))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.91/1.68  tff(c_24, plain, (![C_20, A_18, B_19]: (k1_funct_1(C_20, A_18)=B_19 | ~r2_hidden(k4_tarski(A_18, B_19), C_20) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.91/1.68  tff(c_1435, plain, (![C_223, A_224, B_225]: (k1_funct_1(C_223, '#skF_2'(A_224, B_225, C_223))=A_224 | ~v1_funct_1(C_223) | ~r2_hidden(A_224, k9_relat_1(C_223, B_225)) | ~v1_relat_1(C_223))), inference(resolution, [status(thm)], [c_651, c_24])).
% 3.91/1.68  tff(c_1439, plain, (![A_224]: (k1_funct_1('#skF_6', '#skF_2'(A_224, '#skF_4', '#skF_6'))=A_224 | ~v1_funct_1('#skF_6') | ~r2_hidden(A_224, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_931, c_1435])).
% 3.91/1.68  tff(c_1465, plain, (![A_226]: (k1_funct_1('#skF_6', '#skF_2'(A_226, '#skF_4', '#skF_6'))=A_226 | ~r2_hidden(A_226, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_58, c_1439])).
% 3.91/1.68  tff(c_1484, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))='#skF_3'), inference(resolution, [status(thm)], [c_157, c_1465])).
% 3.91/1.68  tff(c_1496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1048, c_1484])).
% 3.91/1.68  tff(c_1497, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_890])).
% 3.91/1.68  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.68  tff(c_1505, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1497, c_6])).
% 3.91/1.68  tff(c_1507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_1505])).
% 3.91/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.68  
% 3.91/1.68  Inference rules
% 3.91/1.68  ----------------------
% 3.91/1.68  #Ref     : 0
% 3.91/1.68  #Sup     : 297
% 3.91/1.68  #Fact    : 0
% 3.91/1.68  #Define  : 0
% 3.91/1.68  #Split   : 2
% 3.91/1.68  #Chain   : 0
% 3.91/1.68  #Close   : 0
% 3.91/1.68  
% 3.91/1.68  Ordering : KBO
% 3.91/1.68  
% 3.91/1.68  Simplification rules
% 3.91/1.68  ----------------------
% 3.91/1.68  #Subsume      : 56
% 3.91/1.68  #Demod        : 95
% 3.91/1.68  #Tautology    : 19
% 3.91/1.68  #SimpNegUnit  : 11
% 3.91/1.68  #BackRed      : 12
% 3.91/1.68  
% 3.91/1.68  #Partial instantiations: 0
% 3.91/1.68  #Strategies tried      : 1
% 3.91/1.68  
% 3.91/1.68  Timing (in seconds)
% 3.91/1.68  ----------------------
% 3.91/1.68  Preprocessing        : 0.32
% 3.91/1.68  Parsing              : 0.17
% 3.91/1.68  CNF conversion       : 0.02
% 3.91/1.68  Main loop            : 0.51
% 3.91/1.68  Inferencing          : 0.19
% 3.91/1.68  Reduction            : 0.14
% 3.91/1.68  Demodulation         : 0.09
% 3.91/1.68  BG Simplification    : 0.03
% 3.91/1.68  Subsumption          : 0.11
% 3.91/1.68  Abstraction          : 0.03
% 3.91/1.68  MUC search           : 0.00
% 3.91/1.68  Cooper               : 0.00
% 3.91/1.68  Total                : 0.87
% 3.91/1.68  Index Insertion      : 0.00
% 3.91/1.68  Index Deletion       : 0.00
% 3.91/1.68  Index Matching       : 0.00
% 3.91/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
