%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:00 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 178 expanded)
%              Number of leaves         :   37 (  77 expanded)
%              Depth                    :   11
%              Number of atoms          :  142 ( 409 expanded)
%              Number of equality atoms :   35 (  99 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_82,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_91,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_82])).

tff(c_101,plain,(
    ! [C_46,B_47,A_48] :
      ( v1_xboole_0(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(B_47,A_48)))
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_110,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_101])).

tff(c_111,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_127,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_relset_1(A_54,B_55,C_56) = k2_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_136,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_127])).

tff(c_48,plain,(
    r2_hidden('#skF_3',k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_139,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_48])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_113,plain,(
    ! [A_51,B_52,C_53] :
      ( k1_relset_1(A_51,B_52,C_53) = k1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_122,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_113])).

tff(c_532,plain,(
    ! [B_137,A_138,C_139] :
      ( k1_xboole_0 = B_137
      | k1_relset_1(A_138,B_137,C_139) = A_138
      | ~ v1_funct_2(C_139,A_138,B_137)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_539,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_532])).

tff(c_543,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_122,c_539])).

tff(c_544,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_543])).

tff(c_18,plain,(
    ! [A_13] :
      ( k9_relat_1(A_13,k1_relat_1(A_13)) = k2_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_562,plain,
    ( k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_18])).

tff(c_574,plain,(
    k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_562])).

tff(c_155,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden('#skF_2'(A_61,B_62,C_63),B_62)
      | ~ r2_hidden(A_61,k9_relat_1(C_63,B_62))
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_162,plain,(
    ! [A_61,B_62,C_63] :
      ( m1_subset_1('#skF_2'(A_61,B_62,C_63),B_62)
      | ~ r2_hidden(A_61,k9_relat_1(C_63,B_62))
      | ~ v1_relat_1(C_63) ) ),
    inference(resolution,[status(thm)],[c_155,c_8])).

tff(c_606,plain,(
    ! [A_61] :
      ( m1_subset_1('#skF_2'(A_61,'#skF_4','#skF_6'),'#skF_4')
      | ~ r2_hidden(A_61,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_162])).

tff(c_641,plain,(
    ! [A_140] :
      ( m1_subset_1('#skF_2'(A_140,'#skF_4','#skF_6'),'#skF_4')
      | ~ r2_hidden(A_140,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_606])).

tff(c_664,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_139,c_641])).

tff(c_46,plain,(
    ! [E_34] :
      ( k1_funct_1('#skF_6',E_34) != '#skF_3'
      | ~ m1_subset_1(E_34,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_671,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_664,c_46])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_307,plain,(
    ! [A_114,B_115,C_116] :
      ( r2_hidden(k4_tarski('#skF_2'(A_114,B_115,C_116),A_114),C_116)
      | ~ r2_hidden(A_114,k9_relat_1(C_116,B_115))
      | ~ v1_relat_1(C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [C_16,A_14,B_15] :
      ( k1_funct_1(C_16,A_14) = B_15
      | ~ r2_hidden(k4_tarski(A_14,B_15),C_16)
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1051,plain,(
    ! [C_186,A_187,B_188] :
      ( k1_funct_1(C_186,'#skF_2'(A_187,B_188,C_186)) = A_187
      | ~ v1_funct_1(C_186)
      | ~ r2_hidden(A_187,k9_relat_1(C_186,B_188))
      | ~ v1_relat_1(C_186) ) ),
    inference(resolution,[status(thm)],[c_307,c_22])).

tff(c_1053,plain,(
    ! [A_187] :
      ( k1_funct_1('#skF_6','#skF_2'(A_187,'#skF_4','#skF_6')) = A_187
      | ~ v1_funct_1('#skF_6')
      | ~ r2_hidden(A_187,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_1051])).

tff(c_1074,plain,(
    ! [A_189] :
      ( k1_funct_1('#skF_6','#skF_2'(A_189,'#skF_4','#skF_6')) = A_189
      | ~ r2_hidden(A_189,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_54,c_1053])).

tff(c_1089,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_139,c_1074])).

tff(c_1100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_671,c_1089])).

tff(c_1101,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_543])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1108,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_6])).

tff(c_1110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_1108])).

tff(c_1111,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1308,plain,(
    ! [A_255,B_256,C_257] :
      ( r2_hidden(k4_tarski('#skF_2'(A_255,B_256,C_257),A_255),C_257)
      | ~ r2_hidden(A_255,k9_relat_1(C_257,B_256))
      | ~ v1_relat_1(C_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1359,plain,(
    ! [C_258,A_259,B_260] :
      ( ~ v1_xboole_0(C_258)
      | ~ r2_hidden(A_259,k9_relat_1(C_258,B_260))
      | ~ v1_relat_1(C_258) ) ),
    inference(resolution,[status(thm)],[c_1308,c_2])).

tff(c_1435,plain,(
    ! [C_263,B_264] :
      ( ~ v1_xboole_0(C_263)
      | ~ v1_relat_1(C_263)
      | v1_xboole_0(k9_relat_1(C_263,B_264)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1359])).

tff(c_1439,plain,(
    ! [A_265] :
      ( ~ v1_xboole_0(A_265)
      | ~ v1_relat_1(A_265)
      | v1_xboole_0(k2_relat_1(A_265))
      | ~ v1_relat_1(A_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1435])).

tff(c_1128,plain,(
    ! [A_195,B_196,C_197] :
      ( k2_relset_1(A_195,B_196,C_197) = k2_relat_1(C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1137,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_1128])).

tff(c_59,plain,(
    ~ v1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_1139,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1137,c_59])).

tff(c_1442,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1439,c_1139])).

tff(c_1446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1111,c_1442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:53:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.53  
% 3.38/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.53  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.38/1.53  
% 3.38/1.53  %Foreground sorts:
% 3.38/1.53  
% 3.38/1.53  
% 3.38/1.53  %Background operators:
% 3.38/1.53  
% 3.38/1.53  
% 3.38/1.53  %Foreground operators:
% 3.38/1.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.38/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.38/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.38/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.38/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.38/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.38/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.38/1.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.38/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.38/1.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.38/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.38/1.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.38/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.38/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.38/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.38/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.38/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.53  
% 3.69/1.55  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 3.69/1.55  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.69/1.55  tff(f_72, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.69/1.55  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.69/1.55  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.69/1.55  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.69/1.55  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.69/1.55  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.69/1.55  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.69/1.55  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.69/1.55  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.69/1.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.69/1.55  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.55  tff(c_82, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.69/1.55  tff(c_91, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_82])).
% 3.69/1.55  tff(c_101, plain, (![C_46, B_47, A_48]: (v1_xboole_0(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(B_47, A_48))) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.69/1.55  tff(c_110, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_101])).
% 3.69/1.55  tff(c_111, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_110])).
% 3.69/1.55  tff(c_127, plain, (![A_54, B_55, C_56]: (k2_relset_1(A_54, B_55, C_56)=k2_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.69/1.55  tff(c_136, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_127])).
% 3.69/1.55  tff(c_48, plain, (r2_hidden('#skF_3', k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.55  tff(c_139, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_48])).
% 3.69/1.55  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.55  tff(c_113, plain, (![A_51, B_52, C_53]: (k1_relset_1(A_51, B_52, C_53)=k1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.69/1.55  tff(c_122, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_113])).
% 3.69/1.55  tff(c_532, plain, (![B_137, A_138, C_139]: (k1_xboole_0=B_137 | k1_relset_1(A_138, B_137, C_139)=A_138 | ~v1_funct_2(C_139, A_138, B_137) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.69/1.55  tff(c_539, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_532])).
% 3.69/1.55  tff(c_543, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_122, c_539])).
% 3.69/1.55  tff(c_544, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_543])).
% 3.69/1.55  tff(c_18, plain, (![A_13]: (k9_relat_1(A_13, k1_relat_1(A_13))=k2_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.69/1.55  tff(c_562, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_544, c_18])).
% 3.69/1.55  tff(c_574, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_562])).
% 3.69/1.55  tff(c_155, plain, (![A_61, B_62, C_63]: (r2_hidden('#skF_2'(A_61, B_62, C_63), B_62) | ~r2_hidden(A_61, k9_relat_1(C_63, B_62)) | ~v1_relat_1(C_63))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.69/1.55  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.69/1.55  tff(c_162, plain, (![A_61, B_62, C_63]: (m1_subset_1('#skF_2'(A_61, B_62, C_63), B_62) | ~r2_hidden(A_61, k9_relat_1(C_63, B_62)) | ~v1_relat_1(C_63))), inference(resolution, [status(thm)], [c_155, c_8])).
% 3.69/1.55  tff(c_606, plain, (![A_61]: (m1_subset_1('#skF_2'(A_61, '#skF_4', '#skF_6'), '#skF_4') | ~r2_hidden(A_61, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_574, c_162])).
% 3.69/1.55  tff(c_641, plain, (![A_140]: (m1_subset_1('#skF_2'(A_140, '#skF_4', '#skF_6'), '#skF_4') | ~r2_hidden(A_140, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_606])).
% 3.69/1.55  tff(c_664, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_139, c_641])).
% 3.69/1.55  tff(c_46, plain, (![E_34]: (k1_funct_1('#skF_6', E_34)!='#skF_3' | ~m1_subset_1(E_34, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.55  tff(c_671, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))!='#skF_3'), inference(resolution, [status(thm)], [c_664, c_46])).
% 3.69/1.55  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.55  tff(c_307, plain, (![A_114, B_115, C_116]: (r2_hidden(k4_tarski('#skF_2'(A_114, B_115, C_116), A_114), C_116) | ~r2_hidden(A_114, k9_relat_1(C_116, B_115)) | ~v1_relat_1(C_116))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.69/1.55  tff(c_22, plain, (![C_16, A_14, B_15]: (k1_funct_1(C_16, A_14)=B_15 | ~r2_hidden(k4_tarski(A_14, B_15), C_16) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.69/1.55  tff(c_1051, plain, (![C_186, A_187, B_188]: (k1_funct_1(C_186, '#skF_2'(A_187, B_188, C_186))=A_187 | ~v1_funct_1(C_186) | ~r2_hidden(A_187, k9_relat_1(C_186, B_188)) | ~v1_relat_1(C_186))), inference(resolution, [status(thm)], [c_307, c_22])).
% 3.69/1.55  tff(c_1053, plain, (![A_187]: (k1_funct_1('#skF_6', '#skF_2'(A_187, '#skF_4', '#skF_6'))=A_187 | ~v1_funct_1('#skF_6') | ~r2_hidden(A_187, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_574, c_1051])).
% 3.69/1.55  tff(c_1074, plain, (![A_189]: (k1_funct_1('#skF_6', '#skF_2'(A_189, '#skF_4', '#skF_6'))=A_189 | ~r2_hidden(A_189, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_54, c_1053])).
% 3.69/1.55  tff(c_1089, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))='#skF_3'), inference(resolution, [status(thm)], [c_139, c_1074])).
% 3.69/1.55  tff(c_1100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_671, c_1089])).
% 3.69/1.55  tff(c_1101, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_543])).
% 3.69/1.55  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.55  tff(c_1108, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_6])).
% 3.69/1.55  tff(c_1110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_1108])).
% 3.69/1.55  tff(c_1111, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_110])).
% 3.69/1.55  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.69/1.55  tff(c_1308, plain, (![A_255, B_256, C_257]: (r2_hidden(k4_tarski('#skF_2'(A_255, B_256, C_257), A_255), C_257) | ~r2_hidden(A_255, k9_relat_1(C_257, B_256)) | ~v1_relat_1(C_257))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.69/1.55  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.69/1.55  tff(c_1359, plain, (![C_258, A_259, B_260]: (~v1_xboole_0(C_258) | ~r2_hidden(A_259, k9_relat_1(C_258, B_260)) | ~v1_relat_1(C_258))), inference(resolution, [status(thm)], [c_1308, c_2])).
% 3.69/1.55  tff(c_1435, plain, (![C_263, B_264]: (~v1_xboole_0(C_263) | ~v1_relat_1(C_263) | v1_xboole_0(k9_relat_1(C_263, B_264)))), inference(resolution, [status(thm)], [c_4, c_1359])).
% 3.69/1.55  tff(c_1439, plain, (![A_265]: (~v1_xboole_0(A_265) | ~v1_relat_1(A_265) | v1_xboole_0(k2_relat_1(A_265)) | ~v1_relat_1(A_265))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1435])).
% 3.69/1.55  tff(c_1128, plain, (![A_195, B_196, C_197]: (k2_relset_1(A_195, B_196, C_197)=k2_relat_1(C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.69/1.55  tff(c_1137, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_1128])).
% 3.69/1.55  tff(c_59, plain, (~v1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_2])).
% 3.69/1.55  tff(c_1139, plain, (~v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1137, c_59])).
% 3.69/1.55  tff(c_1442, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1439, c_1139])).
% 3.69/1.55  tff(c_1446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_1111, c_1442])).
% 3.69/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.55  
% 3.69/1.55  Inference rules
% 3.69/1.55  ----------------------
% 3.69/1.55  #Ref     : 0
% 3.69/1.55  #Sup     : 286
% 3.69/1.55  #Fact    : 0
% 3.69/1.55  #Define  : 0
% 3.69/1.55  #Split   : 3
% 3.69/1.55  #Chain   : 0
% 3.69/1.55  #Close   : 0
% 3.69/1.55  
% 3.69/1.55  Ordering : KBO
% 3.69/1.55  
% 3.69/1.55  Simplification rules
% 3.69/1.55  ----------------------
% 3.69/1.55  #Subsume      : 49
% 3.69/1.55  #Demod        : 89
% 3.69/1.55  #Tautology    : 26
% 3.69/1.55  #SimpNegUnit  : 10
% 3.69/1.55  #BackRed      : 14
% 3.69/1.55  
% 3.69/1.55  #Partial instantiations: 0
% 3.69/1.55  #Strategies tried      : 1
% 3.69/1.55  
% 3.69/1.55  Timing (in seconds)
% 3.69/1.55  ----------------------
% 3.69/1.55  Preprocessing        : 0.31
% 3.69/1.55  Parsing              : 0.16
% 3.69/1.55  CNF conversion       : 0.02
% 3.69/1.55  Main loop            : 0.52
% 3.69/1.55  Inferencing          : 0.20
% 3.69/1.55  Reduction            : 0.13
% 3.69/1.55  Demodulation         : 0.09
% 3.69/1.55  BG Simplification    : 0.03
% 3.69/1.55  Subsumption          : 0.11
% 3.69/1.55  Abstraction          : 0.03
% 3.69/1.55  MUC search           : 0.00
% 3.69/1.55  Cooper               : 0.00
% 3.69/1.55  Total                : 0.87
% 3.69/1.55  Index Insertion      : 0.00
% 3.69/1.55  Index Deletion       : 0.00
% 3.69/1.55  Index Matching       : 0.00
% 3.69/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
