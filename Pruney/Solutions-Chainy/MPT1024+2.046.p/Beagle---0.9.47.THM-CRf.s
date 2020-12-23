%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:28 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 151 expanded)
%              Number of leaves         :   36 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 367 expanded)
%              Number of equality atoms :   30 (  77 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_89,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_104,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k7_relset_1(A_88,B_89,C_90,D_91) = k9_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_113,plain,(
    ! [D_92] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_92) = k9_relat_1('#skF_8',D_92) ),
    inference(resolution,[status(thm)],[c_56,c_104])).

tff(c_34,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( m1_subset_1(k7_relset_1(A_51,B_52,C_53,D_54),k1_zfmisc_1(B_52))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_119,plain,(
    ! [D_92] :
      ( m1_subset_1(k9_relat_1('#skF_8',D_92),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_34])).

tff(c_127,plain,(
    ! [D_93] : m1_subset_1(k9_relat_1('#skF_8',D_93),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_119])).

tff(c_4,plain,(
    ! [C_3,B_2,A_1] :
      ( ~ v1_xboole_0(C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_133,plain,(
    ! [A_1,D_93] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden(A_1,k9_relat_1('#skF_8',D_93)) ) ),
    inference(resolution,[status(thm)],[c_127,c_4])).

tff(c_136,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_8,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_62,plain,(
    ! [B_72,A_73] :
      ( v1_relat_1(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_65,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_56,c_62])).

tff(c_68,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_65])).

tff(c_60,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_12,plain,(
    ! [A_9,B_32,D_47] :
      ( k1_funct_1(A_9,'#skF_4'(A_9,B_32,k9_relat_1(A_9,B_32),D_47)) = D_47
      | ~ r2_hidden(D_47,k9_relat_1(A_9,B_32))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_76,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_relset_1(A_79,B_80,C_81) = k1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_80,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_76])).

tff(c_163,plain,(
    ! [B_107,A_108,C_109] :
      ( k1_xboole_0 = B_107
      | k1_relset_1(A_108,B_107,C_109) = A_108
      | ~ v1_funct_2(C_109,A_108,B_107)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_170,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_163])).

tff(c_174,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_80,c_170])).

tff(c_175,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_208,plain,(
    ! [A_119,B_120,D_121] :
      ( r2_hidden('#skF_4'(A_119,B_120,k9_relat_1(A_119,B_120),D_121),k1_relat_1(A_119))
      | ~ r2_hidden(D_121,k9_relat_1(A_119,B_120))
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_211,plain,(
    ! [B_120,D_121] :
      ( r2_hidden('#skF_4'('#skF_8',B_120,k9_relat_1('#skF_8',B_120),D_121),'#skF_5')
      | ~ r2_hidden(D_121,k9_relat_1('#skF_8',B_120))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_208])).

tff(c_213,plain,(
    ! [B_120,D_121] :
      ( r2_hidden('#skF_4'('#skF_8',B_120,k9_relat_1('#skF_8',B_120),D_121),'#skF_5')
      | ~ r2_hidden(D_121,k9_relat_1('#skF_8',B_120)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_60,c_211])).

tff(c_198,plain,(
    ! [A_116,B_117,D_118] :
      ( r2_hidden('#skF_4'(A_116,B_117,k9_relat_1(A_116,B_117),D_118),B_117)
      | ~ r2_hidden(D_118,k9_relat_1(A_116,B_117))
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    ! [F_69] :
      ( k1_funct_1('#skF_8',F_69) != '#skF_9'
      | ~ r2_hidden(F_69,'#skF_7')
      | ~ r2_hidden(F_69,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_227,plain,(
    ! [A_127,D_128] :
      ( k1_funct_1('#skF_8','#skF_4'(A_127,'#skF_7',k9_relat_1(A_127,'#skF_7'),D_128)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_127,'#skF_7',k9_relat_1(A_127,'#skF_7'),D_128),'#skF_5')
      | ~ r2_hidden(D_128,k9_relat_1(A_127,'#skF_7'))
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(resolution,[status(thm)],[c_198,c_52])).

tff(c_231,plain,(
    ! [D_121] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_121)) != '#skF_9'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_121,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_213,c_227])).

tff(c_235,plain,(
    ! [D_129] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_129)) != '#skF_9'
      | ~ r2_hidden(D_129,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_60,c_231])).

tff(c_239,plain,(
    ! [D_47] :
      ( D_47 != '#skF_9'
      | ~ r2_hidden(D_47,k9_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_47,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_235])).

tff(c_242,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_60,c_239])).

tff(c_111,plain,(
    ! [D_91] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_91) = k9_relat_1('#skF_8',D_91) ),
    inference(resolution,[status(thm)],[c_56,c_104])).

tff(c_54,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_112,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_54])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_112])).

tff(c_245,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_252,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_2])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_252])).

tff(c_255,plain,(
    ! [A_1,D_93] : ~ r2_hidden(A_1,k9_relat_1('#skF_8',D_93)) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.28  
% 2.35/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.35/1.29  
% 2.35/1.29  %Foreground sorts:
% 2.35/1.29  
% 2.35/1.29  
% 2.35/1.29  %Background operators:
% 2.35/1.29  
% 2.35/1.29  
% 2.35/1.29  %Foreground operators:
% 2.35/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.35/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.35/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.29  tff('#skF_7', type, '#skF_7': $i).
% 2.35/1.29  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.35/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.35/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.35/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.35/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.35/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.35/1.29  tff('#skF_9', type, '#skF_9': $i).
% 2.35/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.35/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.35/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.35/1.29  tff('#skF_8', type, '#skF_8': $i).
% 2.35/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.35/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.35/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.35/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.29  
% 2.35/1.30  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 2.35/1.30  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.35/1.30  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 2.35/1.30  tff(f_33, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.35/1.30  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.35/1.30  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.35/1.30  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 2.35/1.30  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.35/1.30  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.35/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.35/1.30  tff(c_56, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.35/1.30  tff(c_104, plain, (![A_88, B_89, C_90, D_91]: (k7_relset_1(A_88, B_89, C_90, D_91)=k9_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.35/1.30  tff(c_113, plain, (![D_92]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_92)=k9_relat_1('#skF_8', D_92))), inference(resolution, [status(thm)], [c_56, c_104])).
% 2.35/1.30  tff(c_34, plain, (![A_51, B_52, C_53, D_54]: (m1_subset_1(k7_relset_1(A_51, B_52, C_53, D_54), k1_zfmisc_1(B_52)) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.35/1.30  tff(c_119, plain, (![D_92]: (m1_subset_1(k9_relat_1('#skF_8', D_92), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_113, c_34])).
% 2.35/1.30  tff(c_127, plain, (![D_93]: (m1_subset_1(k9_relat_1('#skF_8', D_93), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_119])).
% 2.35/1.30  tff(c_4, plain, (![C_3, B_2, A_1]: (~v1_xboole_0(C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.35/1.30  tff(c_133, plain, (![A_1, D_93]: (~v1_xboole_0('#skF_6') | ~r2_hidden(A_1, k9_relat_1('#skF_8', D_93)))), inference(resolution, [status(thm)], [c_127, c_4])).
% 2.35/1.30  tff(c_136, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_133])).
% 2.35/1.30  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.35/1.30  tff(c_62, plain, (![B_72, A_73]: (v1_relat_1(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.35/1.30  tff(c_65, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_56, c_62])).
% 2.35/1.30  tff(c_68, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_65])).
% 2.35/1.30  tff(c_60, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.35/1.30  tff(c_12, plain, (![A_9, B_32, D_47]: (k1_funct_1(A_9, '#skF_4'(A_9, B_32, k9_relat_1(A_9, B_32), D_47))=D_47 | ~r2_hidden(D_47, k9_relat_1(A_9, B_32)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.35/1.30  tff(c_58, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.35/1.30  tff(c_76, plain, (![A_79, B_80, C_81]: (k1_relset_1(A_79, B_80, C_81)=k1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.35/1.30  tff(c_80, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_76])).
% 2.35/1.30  tff(c_163, plain, (![B_107, A_108, C_109]: (k1_xboole_0=B_107 | k1_relset_1(A_108, B_107, C_109)=A_108 | ~v1_funct_2(C_109, A_108, B_107) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.35/1.30  tff(c_170, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_163])).
% 2.35/1.30  tff(c_174, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_80, c_170])).
% 2.35/1.30  tff(c_175, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_174])).
% 2.35/1.30  tff(c_208, plain, (![A_119, B_120, D_121]: (r2_hidden('#skF_4'(A_119, B_120, k9_relat_1(A_119, B_120), D_121), k1_relat_1(A_119)) | ~r2_hidden(D_121, k9_relat_1(A_119, B_120)) | ~v1_funct_1(A_119) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.35/1.30  tff(c_211, plain, (![B_120, D_121]: (r2_hidden('#skF_4'('#skF_8', B_120, k9_relat_1('#skF_8', B_120), D_121), '#skF_5') | ~r2_hidden(D_121, k9_relat_1('#skF_8', B_120)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_175, c_208])).
% 2.35/1.30  tff(c_213, plain, (![B_120, D_121]: (r2_hidden('#skF_4'('#skF_8', B_120, k9_relat_1('#skF_8', B_120), D_121), '#skF_5') | ~r2_hidden(D_121, k9_relat_1('#skF_8', B_120)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_60, c_211])).
% 2.35/1.30  tff(c_198, plain, (![A_116, B_117, D_118]: (r2_hidden('#skF_4'(A_116, B_117, k9_relat_1(A_116, B_117), D_118), B_117) | ~r2_hidden(D_118, k9_relat_1(A_116, B_117)) | ~v1_funct_1(A_116) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.35/1.30  tff(c_52, plain, (![F_69]: (k1_funct_1('#skF_8', F_69)!='#skF_9' | ~r2_hidden(F_69, '#skF_7') | ~r2_hidden(F_69, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.35/1.30  tff(c_227, plain, (![A_127, D_128]: (k1_funct_1('#skF_8', '#skF_4'(A_127, '#skF_7', k9_relat_1(A_127, '#skF_7'), D_128))!='#skF_9' | ~r2_hidden('#skF_4'(A_127, '#skF_7', k9_relat_1(A_127, '#skF_7'), D_128), '#skF_5') | ~r2_hidden(D_128, k9_relat_1(A_127, '#skF_7')) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(resolution, [status(thm)], [c_198, c_52])).
% 2.35/1.30  tff(c_231, plain, (![D_121]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_121))!='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_121, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_213, c_227])).
% 2.35/1.30  tff(c_235, plain, (![D_129]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_129))!='#skF_9' | ~r2_hidden(D_129, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_60, c_231])).
% 2.35/1.30  tff(c_239, plain, (![D_47]: (D_47!='#skF_9' | ~r2_hidden(D_47, k9_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_47, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_235])).
% 2.35/1.30  tff(c_242, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_60, c_239])).
% 2.35/1.30  tff(c_111, plain, (![D_91]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_91)=k9_relat_1('#skF_8', D_91))), inference(resolution, [status(thm)], [c_56, c_104])).
% 2.35/1.30  tff(c_54, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.35/1.30  tff(c_112, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_54])).
% 2.35/1.30  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_242, c_112])).
% 2.35/1.30  tff(c_245, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_174])).
% 2.35/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.35/1.30  tff(c_252, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_245, c_2])).
% 2.35/1.30  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_252])).
% 2.35/1.30  tff(c_255, plain, (![A_1, D_93]: (~r2_hidden(A_1, k9_relat_1('#skF_8', D_93)))), inference(splitRight, [status(thm)], [c_133])).
% 2.35/1.30  tff(c_258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_112])).
% 2.35/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.30  
% 2.35/1.30  Inference rules
% 2.35/1.30  ----------------------
% 2.35/1.30  #Ref     : 0
% 2.35/1.30  #Sup     : 37
% 2.35/1.30  #Fact    : 0
% 2.35/1.30  #Define  : 0
% 2.35/1.30  #Split   : 4
% 2.35/1.30  #Chain   : 0
% 2.35/1.30  #Close   : 0
% 2.35/1.30  
% 2.35/1.30  Ordering : KBO
% 2.35/1.30  
% 2.35/1.30  Simplification rules
% 2.35/1.30  ----------------------
% 2.35/1.30  #Subsume      : 2
% 2.35/1.30  #Demod        : 35
% 2.35/1.30  #Tautology    : 11
% 2.35/1.30  #SimpNegUnit  : 3
% 2.35/1.30  #BackRed      : 10
% 2.35/1.30  
% 2.35/1.30  #Partial instantiations: 0
% 2.35/1.30  #Strategies tried      : 1
% 2.35/1.30  
% 2.35/1.30  Timing (in seconds)
% 2.35/1.30  ----------------------
% 2.35/1.31  Preprocessing        : 0.33
% 2.35/1.31  Parsing              : 0.16
% 2.35/1.31  CNF conversion       : 0.03
% 2.35/1.31  Main loop            : 0.21
% 2.35/1.31  Inferencing          : 0.07
% 2.35/1.31  Reduction            : 0.06
% 2.35/1.31  Demodulation         : 0.05
% 2.35/1.31  BG Simplification    : 0.02
% 2.35/1.31  Subsumption          : 0.04
% 2.35/1.31  Abstraction          : 0.02
% 2.35/1.31  MUC search           : 0.00
% 2.35/1.31  Cooper               : 0.00
% 2.35/1.31  Total                : 0.58
% 2.35/1.31  Index Insertion      : 0.00
% 2.35/1.31  Index Deletion       : 0.00
% 2.35/1.31  Index Matching       : 0.00
% 2.35/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
