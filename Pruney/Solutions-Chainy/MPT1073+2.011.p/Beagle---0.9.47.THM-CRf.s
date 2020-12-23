%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:59 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 128 expanded)
%              Number of leaves         :   42 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 274 expanded)
%              Number of equality atoms :   27 (  63 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_64,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_161,plain,(
    ! [C_96,B_97,A_98] :
      ( v5_relat_1(C_96,B_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_175,plain,(
    v5_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_161])).

tff(c_97,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_106,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_64,c_97])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_251,plain,(
    ! [A_114,B_115,C_116] :
      ( k2_relset_1(A_114,B_115,C_116) = k2_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_270,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_64,c_251])).

tff(c_62,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_8','#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_183,plain,(
    ! [C_104,B_105,A_106] :
      ( r2_hidden(C_104,B_105)
      | ~ r2_hidden(C_104,A_106)
      | ~ r1_tarski(A_106,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_192,plain,(
    ! [B_105] :
      ( r2_hidden('#skF_7',B_105)
      | ~ r1_tarski(k2_relset_1('#skF_8','#skF_9','#skF_10'),B_105) ) ),
    inference(resolution,[status(thm)],[c_62,c_183])).

tff(c_291,plain,(
    ! [B_117] :
      ( r2_hidden('#skF_7',B_117)
      | ~ r1_tarski(k2_relat_1('#skF_10'),B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_192])).

tff(c_295,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_7',A_12)
      | ~ v5_relat_1('#skF_10',A_12)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_18,c_291])).

tff(c_310,plain,(
    ! [A_118] :
      ( r2_hidden('#skF_7',A_118)
      | ~ v5_relat_1('#skF_10',A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_295])).

tff(c_318,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_175,c_310])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_332,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_318,c_2])).

tff(c_68,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_22,plain,(
    ! [A_14,C_50] :
      ( k1_funct_1(A_14,'#skF_6'(A_14,k2_relat_1(A_14),C_50)) = C_50
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_66,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_333,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_352,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_64,c_333])).

tff(c_1248,plain,(
    ! [B_265,A_266,C_267] :
      ( k1_xboole_0 = B_265
      | k1_relset_1(A_266,B_265,C_267) = A_266
      | ~ v1_funct_2(C_267,A_266,B_265)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_266,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1271,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_1248])).

tff(c_1279,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_352,c_1271])).

tff(c_1280,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1279])).

tff(c_836,plain,(
    ! [A_216,C_217] :
      ( r2_hidden('#skF_6'(A_216,k2_relat_1(A_216),C_217),k1_relat_1(A_216))
      | ~ r2_hidden(C_217,k2_relat_1(A_216))
      | ~ v1_funct_1(A_216)
      | ~ v1_relat_1(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_850,plain,(
    ! [A_216,C_217] :
      ( m1_subset_1('#skF_6'(A_216,k2_relat_1(A_216),C_217),k1_relat_1(A_216))
      | ~ r2_hidden(C_217,k2_relat_1(A_216))
      | ~ v1_funct_1(A_216)
      | ~ v1_relat_1(A_216) ) ),
    inference(resolution,[status(thm)],[c_836,c_14])).

tff(c_1289,plain,(
    ! [C_217] :
      ( m1_subset_1('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_217),'#skF_8')
      | ~ r2_hidden(C_217,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1280,c_850])).

tff(c_1346,plain,(
    ! [C_269] :
      ( m1_subset_1('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_269),'#skF_8')
      | ~ r2_hidden(C_269,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_68,c_1289])).

tff(c_60,plain,(
    ! [E_70] :
      ( k1_funct_1('#skF_10',E_70) != '#skF_7'
      | ~ m1_subset_1(E_70,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1351,plain,(
    ! [C_270] :
      ( k1_funct_1('#skF_10','#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_270)) != '#skF_7'
      | ~ r2_hidden(C_270,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_1346,c_60])).

tff(c_1355,plain,(
    ! [C_50] :
      ( C_50 != '#skF_7'
      | ~ r2_hidden(C_50,k2_relat_1('#skF_10'))
      | ~ r2_hidden(C_50,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1351])).

tff(c_1400,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_68,c_1355])).

tff(c_274,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_62])).

tff(c_1402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1400,c_274])).

tff(c_1403,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1279])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1411,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_12])).

tff(c_1413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_1411])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.70  
% 3.38/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.70  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 3.38/1.70  
% 3.38/1.70  %Foreground sorts:
% 3.38/1.70  
% 3.38/1.70  
% 3.38/1.70  %Background operators:
% 3.38/1.70  
% 3.38/1.70  
% 3.38/1.70  %Foreground operators:
% 3.38/1.70  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.38/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.38/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.70  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.38/1.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.38/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.70  tff('#skF_7', type, '#skF_7': $i).
% 3.38/1.70  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.38/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.70  tff('#skF_10', type, '#skF_10': $i).
% 3.38/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.38/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.38/1.70  tff('#skF_9', type, '#skF_9': $i).
% 3.38/1.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.38/1.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.38/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.38/1.70  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.38/1.70  tff('#skF_8', type, '#skF_8': $i).
% 3.38/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.38/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.38/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.38/1.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.38/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.38/1.70  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.38/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.38/1.70  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.38/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.70  
% 3.38/1.72  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 3.38/1.72  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.38/1.72  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.38/1.72  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.38/1.72  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.38/1.72  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.38/1.72  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.38/1.72  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.38/1.72  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.38/1.72  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.38/1.72  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.38/1.72  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.38/1.72  tff(c_64, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.38/1.72  tff(c_161, plain, (![C_96, B_97, A_98]: (v5_relat_1(C_96, B_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.38/1.72  tff(c_175, plain, (v5_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_64, c_161])).
% 3.38/1.72  tff(c_97, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.38/1.72  tff(c_106, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_64, c_97])).
% 3.38/1.72  tff(c_18, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.38/1.72  tff(c_251, plain, (![A_114, B_115, C_116]: (k2_relset_1(A_114, B_115, C_116)=k2_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.38/1.72  tff(c_270, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_64, c_251])).
% 3.38/1.72  tff(c_62, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_8', '#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.38/1.72  tff(c_183, plain, (![C_104, B_105, A_106]: (r2_hidden(C_104, B_105) | ~r2_hidden(C_104, A_106) | ~r1_tarski(A_106, B_105))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.38/1.72  tff(c_192, plain, (![B_105]: (r2_hidden('#skF_7', B_105) | ~r1_tarski(k2_relset_1('#skF_8', '#skF_9', '#skF_10'), B_105))), inference(resolution, [status(thm)], [c_62, c_183])).
% 3.38/1.72  tff(c_291, plain, (![B_117]: (r2_hidden('#skF_7', B_117) | ~r1_tarski(k2_relat_1('#skF_10'), B_117))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_192])).
% 3.38/1.72  tff(c_295, plain, (![A_12]: (r2_hidden('#skF_7', A_12) | ~v5_relat_1('#skF_10', A_12) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_18, c_291])).
% 3.38/1.72  tff(c_310, plain, (![A_118]: (r2_hidden('#skF_7', A_118) | ~v5_relat_1('#skF_10', A_118))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_295])).
% 3.38/1.72  tff(c_318, plain, (r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_175, c_310])).
% 3.38/1.72  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.38/1.72  tff(c_332, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_318, c_2])).
% 3.38/1.72  tff(c_68, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.38/1.72  tff(c_22, plain, (![A_14, C_50]: (k1_funct_1(A_14, '#skF_6'(A_14, k2_relat_1(A_14), C_50))=C_50 | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.38/1.72  tff(c_66, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.38/1.72  tff(c_333, plain, (![A_119, B_120, C_121]: (k1_relset_1(A_119, B_120, C_121)=k1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.38/1.72  tff(c_352, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_64, c_333])).
% 3.38/1.72  tff(c_1248, plain, (![B_265, A_266, C_267]: (k1_xboole_0=B_265 | k1_relset_1(A_266, B_265, C_267)=A_266 | ~v1_funct_2(C_267, A_266, B_265) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_266, B_265))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.38/1.72  tff(c_1271, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_64, c_1248])).
% 3.38/1.72  tff(c_1279, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_352, c_1271])).
% 3.38/1.72  tff(c_1280, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitLeft, [status(thm)], [c_1279])).
% 3.38/1.72  tff(c_836, plain, (![A_216, C_217]: (r2_hidden('#skF_6'(A_216, k2_relat_1(A_216), C_217), k1_relat_1(A_216)) | ~r2_hidden(C_217, k2_relat_1(A_216)) | ~v1_funct_1(A_216) | ~v1_relat_1(A_216))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.38/1.72  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.38/1.72  tff(c_850, plain, (![A_216, C_217]: (m1_subset_1('#skF_6'(A_216, k2_relat_1(A_216), C_217), k1_relat_1(A_216)) | ~r2_hidden(C_217, k2_relat_1(A_216)) | ~v1_funct_1(A_216) | ~v1_relat_1(A_216))), inference(resolution, [status(thm)], [c_836, c_14])).
% 3.38/1.72  tff(c_1289, plain, (![C_217]: (m1_subset_1('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_217), '#skF_8') | ~r2_hidden(C_217, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1280, c_850])).
% 3.38/1.72  tff(c_1346, plain, (![C_269]: (m1_subset_1('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_269), '#skF_8') | ~r2_hidden(C_269, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_68, c_1289])).
% 3.38/1.72  tff(c_60, plain, (![E_70]: (k1_funct_1('#skF_10', E_70)!='#skF_7' | ~m1_subset_1(E_70, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.38/1.72  tff(c_1351, plain, (![C_270]: (k1_funct_1('#skF_10', '#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_270))!='#skF_7' | ~r2_hidden(C_270, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_1346, c_60])).
% 3.38/1.72  tff(c_1355, plain, (![C_50]: (C_50!='#skF_7' | ~r2_hidden(C_50, k2_relat_1('#skF_10')) | ~r2_hidden(C_50, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1351])).
% 3.38/1.72  tff(c_1400, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_68, c_1355])).
% 3.38/1.72  tff(c_274, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_62])).
% 3.38/1.72  tff(c_1402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1400, c_274])).
% 3.38/1.72  tff(c_1403, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1279])).
% 3.38/1.72  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.38/1.72  tff(c_1411, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_12])).
% 3.38/1.72  tff(c_1413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_332, c_1411])).
% 3.38/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.72  
% 3.38/1.72  Inference rules
% 3.38/1.72  ----------------------
% 3.38/1.72  #Ref     : 0
% 3.38/1.72  #Sup     : 284
% 3.38/1.72  #Fact    : 0
% 3.38/1.72  #Define  : 0
% 3.38/1.72  #Split   : 2
% 3.38/1.72  #Chain   : 0
% 3.38/1.72  #Close   : 0
% 3.38/1.72  
% 3.38/1.72  Ordering : KBO
% 3.38/1.72  
% 3.38/1.72  Simplification rules
% 3.38/1.72  ----------------------
% 3.38/1.72  #Subsume      : 91
% 3.38/1.72  #Demod        : 67
% 3.38/1.72  #Tautology    : 32
% 3.38/1.72  #SimpNegUnit  : 3
% 3.38/1.72  #BackRed      : 14
% 3.38/1.72  
% 3.38/1.72  #Partial instantiations: 0
% 3.38/1.72  #Strategies tried      : 1
% 3.38/1.72  
% 3.38/1.72  Timing (in seconds)
% 3.38/1.72  ----------------------
% 3.38/1.72  Preprocessing        : 0.36
% 3.38/1.72  Parsing              : 0.18
% 3.38/1.72  CNF conversion       : 0.03
% 3.38/1.72  Main loop            : 0.47
% 3.38/1.72  Inferencing          : 0.17
% 3.38/1.72  Reduction            : 0.13
% 3.38/1.72  Demodulation         : 0.09
% 3.38/1.72  BG Simplification    : 0.03
% 3.38/1.72  Subsumption          : 0.10
% 3.38/1.72  Abstraction          : 0.02
% 3.38/1.72  MUC search           : 0.00
% 3.38/1.72  Cooper               : 0.00
% 3.38/1.72  Total                : 0.86
% 3.38/1.72  Index Insertion      : 0.00
% 3.38/1.72  Index Deletion       : 0.00
% 3.38/1.72  Index Matching       : 0.00
% 3.38/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
