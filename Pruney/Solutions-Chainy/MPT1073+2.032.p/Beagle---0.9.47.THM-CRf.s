%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:02 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 120 expanded)
%              Number of leaves         :   36 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  112 ( 264 expanded)
%              Number of equality atoms :   27 (  66 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
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

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_52,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_69,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_73,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_69])).

tff(c_56,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10,plain,(
    ! [A_8,C_44] :
      ( k1_funct_1(A_8,'#skF_4'(A_8,k2_relat_1(A_8),C_44)) = C_44
      | ~ r2_hidden(C_44,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_54,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_106,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_110,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_106])).

tff(c_234,plain,(
    ! [B_118,A_119,C_120] :
      ( k1_xboole_0 = B_118
      | k1_relset_1(A_119,B_118,C_120) = A_119
      | ~ v1_funct_2(C_120,A_119,B_118)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_119,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_241,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_234])).

tff(c_245,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_110,c_241])).

tff(c_246,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_208,plain,(
    ! [A_110,C_111] :
      ( r2_hidden('#skF_4'(A_110,k2_relat_1(A_110),C_111),k1_relat_1(A_110))
      | ~ r2_hidden(C_111,k2_relat_1(A_110))
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_218,plain,(
    ! [A_110,C_111] :
      ( m1_subset_1('#skF_4'(A_110,k2_relat_1(A_110),C_111),k1_relat_1(A_110))
      | ~ r2_hidden(C_111,k2_relat_1(A_110))
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(resolution,[status(thm)],[c_208,c_6])).

tff(c_254,plain,(
    ! [C_111] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_111),'#skF_6')
      | ~ r2_hidden(C_111,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_218])).

tff(c_294,plain,(
    ! [C_125] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_125),'#skF_6')
      | ~ r2_hidden(C_125,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_56,c_254])).

tff(c_48,plain,(
    ! [E_66] :
      ( k1_funct_1('#skF_8',E_66) != '#skF_5'
      | ~ m1_subset_1(E_66,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_299,plain,(
    ! [C_126] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_126)) != '#skF_5'
      | ~ r2_hidden(C_126,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_294,c_48])).

tff(c_303,plain,(
    ! [C_44] :
      ( C_44 != '#skF_5'
      | ~ r2_hidden(C_44,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_44,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_299])).

tff(c_306,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_56,c_303])).

tff(c_80,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_84,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_80])).

tff(c_50,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_88,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_50])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_88])).

tff(c_309,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_316,plain,(
    ! [A_1] : r1_tarski('#skF_7',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_2])).

tff(c_115,plain,(
    ! [A_88,B_89,C_90] :
      ( m1_subset_1(k2_relset_1(A_88,B_89,C_90),k1_zfmisc_1(B_89))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_130,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_115])).

tff(c_135,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_130])).

tff(c_74,plain,(
    ! [C_76,A_77,B_78] :
      ( r2_hidden(C_76,A_77)
      | ~ r2_hidden(C_76,B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_77,plain,(
    ! [A_77] :
      ( r2_hidden('#skF_5',A_77)
      | ~ m1_subset_1(k2_relset_1('#skF_6','#skF_7','#skF_8'),k1_zfmisc_1(A_77)) ) ),
    inference(resolution,[status(thm)],[c_50,c_74])).

tff(c_85,plain,(
    ! [A_77] :
      ( r2_hidden('#skF_5',A_77)
      | ~ m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1(A_77)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_77])).

tff(c_145,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_135,c_85])).

tff(c_26,plain,(
    ! [B_49,A_48] :
      ( ~ r1_tarski(B_49,A_48)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_156,plain,(
    ~ r1_tarski('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_145,c_26])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:14:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.47  
% 2.39/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.47  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.39/1.47  
% 2.39/1.47  %Foreground sorts:
% 2.39/1.47  
% 2.39/1.47  
% 2.39/1.47  %Background operators:
% 2.39/1.47  
% 2.39/1.47  
% 2.39/1.47  %Foreground operators:
% 2.39/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.39/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.39/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.39/1.47  tff('#skF_7', type, '#skF_7': $i).
% 2.39/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.39/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.39/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.39/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.39/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.39/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.39/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.39/1.47  tff('#skF_8', type, '#skF_8': $i).
% 2.39/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.39/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.39/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.39/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.47  
% 2.72/1.49  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 2.72/1.49  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.72/1.49  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.72/1.49  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.72/1.49  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.72/1.49  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.72/1.49  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.72/1.49  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.72/1.49  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.72/1.49  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.72/1.49  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.72/1.49  tff(c_52, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.72/1.49  tff(c_69, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.72/1.49  tff(c_73, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_52, c_69])).
% 2.72/1.49  tff(c_56, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.72/1.49  tff(c_10, plain, (![A_8, C_44]: (k1_funct_1(A_8, '#skF_4'(A_8, k2_relat_1(A_8), C_44))=C_44 | ~r2_hidden(C_44, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.49  tff(c_54, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.72/1.49  tff(c_106, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.72/1.49  tff(c_110, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_52, c_106])).
% 2.72/1.49  tff(c_234, plain, (![B_118, A_119, C_120]: (k1_xboole_0=B_118 | k1_relset_1(A_119, B_118, C_120)=A_119 | ~v1_funct_2(C_120, A_119, B_118) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_119, B_118))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.72/1.49  tff(c_241, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_234])).
% 2.72/1.49  tff(c_245, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_110, c_241])).
% 2.72/1.49  tff(c_246, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_245])).
% 2.72/1.49  tff(c_208, plain, (![A_110, C_111]: (r2_hidden('#skF_4'(A_110, k2_relat_1(A_110), C_111), k1_relat_1(A_110)) | ~r2_hidden(C_111, k2_relat_1(A_110)) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.49  tff(c_6, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.72/1.49  tff(c_218, plain, (![A_110, C_111]: (m1_subset_1('#skF_4'(A_110, k2_relat_1(A_110), C_111), k1_relat_1(A_110)) | ~r2_hidden(C_111, k2_relat_1(A_110)) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(resolution, [status(thm)], [c_208, c_6])).
% 2.72/1.49  tff(c_254, plain, (![C_111]: (m1_subset_1('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_111), '#skF_6') | ~r2_hidden(C_111, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_246, c_218])).
% 2.72/1.49  tff(c_294, plain, (![C_125]: (m1_subset_1('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_125), '#skF_6') | ~r2_hidden(C_125, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_56, c_254])).
% 2.72/1.49  tff(c_48, plain, (![E_66]: (k1_funct_1('#skF_8', E_66)!='#skF_5' | ~m1_subset_1(E_66, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.72/1.49  tff(c_299, plain, (![C_126]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_126))!='#skF_5' | ~r2_hidden(C_126, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_294, c_48])).
% 2.72/1.49  tff(c_303, plain, (![C_44]: (C_44!='#skF_5' | ~r2_hidden(C_44, k2_relat_1('#skF_8')) | ~r2_hidden(C_44, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_299])).
% 2.72/1.49  tff(c_306, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_56, c_303])).
% 2.72/1.49  tff(c_80, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.72/1.49  tff(c_84, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_52, c_80])).
% 2.72/1.49  tff(c_50, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.72/1.49  tff(c_88, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_50])).
% 2.72/1.49  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_306, c_88])).
% 2.72/1.49  tff(c_309, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_245])).
% 2.72/1.49  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.49  tff(c_316, plain, (![A_1]: (r1_tarski('#skF_7', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_2])).
% 2.72/1.49  tff(c_115, plain, (![A_88, B_89, C_90]: (m1_subset_1(k2_relset_1(A_88, B_89, C_90), k1_zfmisc_1(B_89)) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.72/1.49  tff(c_130, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_84, c_115])).
% 2.72/1.49  tff(c_135, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_130])).
% 2.72/1.49  tff(c_74, plain, (![C_76, A_77, B_78]: (r2_hidden(C_76, A_77) | ~r2_hidden(C_76, B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.72/1.49  tff(c_77, plain, (![A_77]: (r2_hidden('#skF_5', A_77) | ~m1_subset_1(k2_relset_1('#skF_6', '#skF_7', '#skF_8'), k1_zfmisc_1(A_77)))), inference(resolution, [status(thm)], [c_50, c_74])).
% 2.72/1.49  tff(c_85, plain, (![A_77]: (r2_hidden('#skF_5', A_77) | ~m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1(A_77)))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_77])).
% 2.72/1.49  tff(c_145, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_135, c_85])).
% 2.72/1.49  tff(c_26, plain, (![B_49, A_48]: (~r1_tarski(B_49, A_48) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.72/1.49  tff(c_156, plain, (~r1_tarski('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_145, c_26])).
% 2.72/1.49  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_316, c_156])).
% 2.72/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.49  
% 2.72/1.49  Inference rules
% 2.72/1.49  ----------------------
% 2.72/1.49  #Ref     : 0
% 2.72/1.49  #Sup     : 57
% 2.72/1.49  #Fact    : 0
% 2.72/1.49  #Define  : 0
% 2.72/1.49  #Split   : 1
% 2.72/1.49  #Chain   : 0
% 2.72/1.49  #Close   : 0
% 2.72/1.49  
% 2.72/1.49  Ordering : KBO
% 2.72/1.49  
% 2.72/1.49  Simplification rules
% 2.72/1.49  ----------------------
% 2.72/1.49  #Subsume      : 4
% 2.72/1.49  #Demod        : 38
% 2.72/1.49  #Tautology    : 15
% 2.72/1.49  #SimpNegUnit  : 1
% 2.72/1.49  #BackRed      : 13
% 2.72/1.49  
% 2.72/1.49  #Partial instantiations: 0
% 2.72/1.49  #Strategies tried      : 1
% 2.72/1.49  
% 2.72/1.49  Timing (in seconds)
% 2.72/1.49  ----------------------
% 2.72/1.49  Preprocessing        : 0.36
% 2.72/1.49  Parsing              : 0.16
% 2.72/1.49  CNF conversion       : 0.03
% 2.72/1.49  Main loop            : 0.30
% 2.72/1.49  Inferencing          : 0.10
% 2.72/1.49  Reduction            : 0.09
% 2.72/1.49  Demodulation         : 0.07
% 2.72/1.49  BG Simplification    : 0.03
% 2.72/1.49  Subsumption          : 0.06
% 2.72/1.49  Abstraction          : 0.02
% 2.72/1.49  MUC search           : 0.00
% 2.72/1.49  Cooper               : 0.00
% 2.72/1.49  Total                : 0.70
% 2.72/1.49  Index Insertion      : 0.00
% 2.72/1.49  Index Deletion       : 0.00
% 2.72/1.49  Index Matching       : 0.00
% 2.72/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
