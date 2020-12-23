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
% DateTime   : Thu Dec  3 10:11:21 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 205 expanded)
%              Number of leaves         :   37 (  87 expanded)
%              Depth                    :    8
%              Number of atoms          :  127 ( 504 expanded)
%              Number of equality atoms :   30 ( 124 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
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

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_174,plain,(
    ! [A_107,B_108,C_109] :
      ( k2_relset_1(A_107,B_108,C_109) = k2_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_178,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_174])).

tff(c_56,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_179,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_56])).

tff(c_219,plain,(
    ! [A_118,B_119,C_120] :
      ( m1_subset_1(k2_relset_1(A_118,B_119,C_120),k1_zfmisc_1(B_119))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_237,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_219])).

tff(c_243,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_237])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_123,plain,(
    ! [C_90,A_91,B_92] :
      ( r2_hidden(C_90,A_91)
      | ~ r2_hidden(C_90,B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_184,plain,(
    ! [A_110,B_111,A_112] :
      ( r2_hidden('#skF_1'(A_110,B_111),A_112)
      | ~ m1_subset_1(A_110,k1_zfmisc_1(A_112))
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_195,plain,(
    ! [A_110,A_112] :
      ( ~ m1_subset_1(A_110,k1_zfmisc_1(A_112))
      | r1_tarski(A_110,A_112) ) ),
    inference(resolution,[status(thm)],[c_184,c_4])).

tff(c_247,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_243,c_195])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_253,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_247,c_8])).

tff(c_258,plain,(
    ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_253])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_165,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_169,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_165])).

tff(c_889,plain,(
    ! [B_236,A_237,C_238] :
      ( k1_xboole_0 = B_236
      | k1_relset_1(A_237,B_236,C_238) = A_237
      | ~ v1_funct_2(C_238,A_237,B_236)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_237,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_896,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_889])).

tff(c_900,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_169,c_896])).

tff(c_901,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_900])).

tff(c_66,plain,(
    ! [D_71] :
      ( r2_hidden('#skF_9'(D_71),'#skF_6')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_116,plain,(
    ! [C_87,B_88,A_89] :
      ( r2_hidden(C_87,B_88)
      | ~ r2_hidden(C_87,A_89)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_122,plain,(
    ! [D_71,B_88] :
      ( r2_hidden('#skF_9'(D_71),B_88)
      | ~ r1_tarski('#skF_6',B_88)
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_116])).

tff(c_104,plain,(
    ! [C_82,A_83,B_84] :
      ( v1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_108,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_104])).

tff(c_62,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_64,plain,(
    ! [D_71] :
      ( k1_funct_1('#skF_8','#skF_9'(D_71)) = D_71
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_288,plain,(
    ! [A_129,D_130] :
      ( r2_hidden(k1_funct_1(A_129,D_130),k2_relat_1(A_129))
      | ~ r2_hidden(D_130,k1_relat_1(A_129))
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_295,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_288])).

tff(c_300,plain,(
    ! [D_131] :
      ( r2_hidden(D_131,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_131),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_131,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_62,c_295])).

tff(c_310,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_122,c_300])).

tff(c_311,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_310])).

tff(c_903,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_901,c_311])).

tff(c_908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_903])).

tff(c_909,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_900])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_922,plain,(
    ! [A_8] : r1_tarski('#skF_7',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_14])).

tff(c_934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_922,c_258])).

tff(c_948,plain,(
    ! [D_239] :
      ( r2_hidden(D_239,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_239,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_982,plain,(
    ! [A_245] :
      ( r1_tarski(A_245,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_245,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_948,c_4])).

tff(c_994,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_982])).

tff(c_1000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_258,c_994])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:38:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.57  
% 3.51/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.57  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 3.51/1.57  
% 3.51/1.57  %Foreground sorts:
% 3.51/1.57  
% 3.51/1.57  
% 3.51/1.57  %Background operators:
% 3.51/1.57  
% 3.51/1.57  
% 3.51/1.57  %Foreground operators:
% 3.51/1.57  tff('#skF_9', type, '#skF_9': $i > $i).
% 3.51/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.51/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.51/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.51/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.51/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.51/1.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.51/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.51/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.51/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.51/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.51/1.57  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.51/1.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.51/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.51/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.51/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.51/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.51/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.51/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.51/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.51/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.51/1.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.51/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.51/1.57  
% 3.68/1.58  tff(f_115, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 3.68/1.58  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.68/1.58  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.68/1.58  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.68/1.58  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.68/1.58  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.68/1.58  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.68/1.58  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.68/1.58  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.68/1.58  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.68/1.58  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.68/1.58  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.68/1.58  tff(c_174, plain, (![A_107, B_108, C_109]: (k2_relset_1(A_107, B_108, C_109)=k2_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.68/1.58  tff(c_178, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_174])).
% 3.68/1.58  tff(c_56, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.68/1.58  tff(c_179, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_56])).
% 3.68/1.58  tff(c_219, plain, (![A_118, B_119, C_120]: (m1_subset_1(k2_relset_1(A_118, B_119, C_120), k1_zfmisc_1(B_119)) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.68/1.58  tff(c_237, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_178, c_219])).
% 3.68/1.58  tff(c_243, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_237])).
% 3.68/1.58  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.68/1.58  tff(c_123, plain, (![C_90, A_91, B_92]: (r2_hidden(C_90, A_91) | ~r2_hidden(C_90, B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.68/1.58  tff(c_184, plain, (![A_110, B_111, A_112]: (r2_hidden('#skF_1'(A_110, B_111), A_112) | ~m1_subset_1(A_110, k1_zfmisc_1(A_112)) | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_6, c_123])).
% 3.68/1.58  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.68/1.58  tff(c_195, plain, (![A_110, A_112]: (~m1_subset_1(A_110, k1_zfmisc_1(A_112)) | r1_tarski(A_110, A_112))), inference(resolution, [status(thm)], [c_184, c_4])).
% 3.68/1.58  tff(c_247, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_243, c_195])).
% 3.68/1.58  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.68/1.58  tff(c_253, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_247, c_8])).
% 3.68/1.58  tff(c_258, plain, (~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_179, c_253])).
% 3.68/1.58  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.68/1.58  tff(c_60, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.68/1.58  tff(c_165, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.68/1.58  tff(c_169, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_165])).
% 3.68/1.58  tff(c_889, plain, (![B_236, A_237, C_238]: (k1_xboole_0=B_236 | k1_relset_1(A_237, B_236, C_238)=A_237 | ~v1_funct_2(C_238, A_237, B_236) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_237, B_236))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.68/1.58  tff(c_896, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_58, c_889])).
% 3.68/1.58  tff(c_900, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_169, c_896])).
% 3.68/1.58  tff(c_901, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_900])).
% 3.68/1.58  tff(c_66, plain, (![D_71]: (r2_hidden('#skF_9'(D_71), '#skF_6') | ~r2_hidden(D_71, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.68/1.58  tff(c_116, plain, (![C_87, B_88, A_89]: (r2_hidden(C_87, B_88) | ~r2_hidden(C_87, A_89) | ~r1_tarski(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.68/1.58  tff(c_122, plain, (![D_71, B_88]: (r2_hidden('#skF_9'(D_71), B_88) | ~r1_tarski('#skF_6', B_88) | ~r2_hidden(D_71, '#skF_7'))), inference(resolution, [status(thm)], [c_66, c_116])).
% 3.68/1.58  tff(c_104, plain, (![C_82, A_83, B_84]: (v1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.68/1.58  tff(c_108, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_104])).
% 3.68/1.58  tff(c_62, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.68/1.58  tff(c_64, plain, (![D_71]: (k1_funct_1('#skF_8', '#skF_9'(D_71))=D_71 | ~r2_hidden(D_71, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.68/1.58  tff(c_288, plain, (![A_129, D_130]: (r2_hidden(k1_funct_1(A_129, D_130), k2_relat_1(A_129)) | ~r2_hidden(D_130, k1_relat_1(A_129)) | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.68/1.58  tff(c_295, plain, (![D_71]: (r2_hidden(D_71, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_288])).
% 3.68/1.58  tff(c_300, plain, (![D_131]: (r2_hidden(D_131, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_131), k1_relat_1('#skF_8')) | ~r2_hidden(D_131, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_62, c_295])).
% 3.68/1.58  tff(c_310, plain, (![D_71]: (r2_hidden(D_71, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_71, '#skF_7'))), inference(resolution, [status(thm)], [c_122, c_300])).
% 3.68/1.58  tff(c_311, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_310])).
% 3.68/1.58  tff(c_903, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_901, c_311])).
% 3.68/1.58  tff(c_908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_903])).
% 3.68/1.58  tff(c_909, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_900])).
% 3.68/1.58  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.68/1.58  tff(c_922, plain, (![A_8]: (r1_tarski('#skF_7', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_909, c_14])).
% 3.68/1.58  tff(c_934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_922, c_258])).
% 3.68/1.58  tff(c_948, plain, (![D_239]: (r2_hidden(D_239, k2_relat_1('#skF_8')) | ~r2_hidden(D_239, '#skF_7'))), inference(splitRight, [status(thm)], [c_310])).
% 3.68/1.58  tff(c_982, plain, (![A_245]: (r1_tarski(A_245, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_245, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_948, c_4])).
% 3.68/1.58  tff(c_994, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_982])).
% 3.68/1.58  tff(c_1000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_258, c_258, c_994])).
% 3.68/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.58  
% 3.68/1.58  Inference rules
% 3.68/1.58  ----------------------
% 3.68/1.58  #Ref     : 0
% 3.68/1.58  #Sup     : 206
% 3.68/1.58  #Fact    : 0
% 3.68/1.58  #Define  : 0
% 3.68/1.58  #Split   : 21
% 3.68/1.58  #Chain   : 0
% 3.68/1.58  #Close   : 0
% 3.68/1.58  
% 3.68/1.58  Ordering : KBO
% 3.68/1.58  
% 3.68/1.58  Simplification rules
% 3.68/1.58  ----------------------
% 3.68/1.58  #Subsume      : 46
% 3.68/1.58  #Demod        : 95
% 3.68/1.58  #Tautology    : 32
% 3.68/1.58  #SimpNegUnit  : 2
% 3.68/1.58  #BackRed      : 41
% 3.68/1.58  
% 3.68/1.58  #Partial instantiations: 0
% 3.68/1.58  #Strategies tried      : 1
% 3.68/1.58  
% 3.68/1.58  Timing (in seconds)
% 3.68/1.58  ----------------------
% 3.68/1.59  Preprocessing        : 0.34
% 3.68/1.59  Parsing              : 0.17
% 3.68/1.59  CNF conversion       : 0.03
% 3.68/1.59  Main loop            : 0.48
% 3.68/1.59  Inferencing          : 0.15
% 3.68/1.59  Reduction            : 0.14
% 3.68/1.59  Demodulation         : 0.09
% 3.68/1.59  BG Simplification    : 0.02
% 3.68/1.59  Subsumption          : 0.13
% 3.68/1.59  Abstraction          : 0.02
% 3.68/1.59  MUC search           : 0.00
% 3.68/1.59  Cooper               : 0.00
% 3.68/1.59  Total                : 0.86
% 3.68/1.59  Index Insertion      : 0.00
% 3.68/1.59  Index Deletion       : 0.00
% 3.68/1.59  Index Matching       : 0.00
% 3.68/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
