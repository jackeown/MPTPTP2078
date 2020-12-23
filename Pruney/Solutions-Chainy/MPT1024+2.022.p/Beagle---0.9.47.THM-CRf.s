%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:24 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 129 expanded)
%              Number of leaves         :   36 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 317 expanded)
%              Number of equality atoms :   29 (  72 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
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

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_67,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_71,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_67])).

tff(c_60,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_8,plain,(
    ! [A_6,B_29,D_44] :
      ( k1_funct_1(A_6,'#skF_4'(A_6,B_29,k9_relat_1(A_6,B_29),D_44)) = D_44
      | ~ r2_hidden(D_44,k9_relat_1(A_6,B_29))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_58,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_79,plain,(
    ! [A_84,B_85,C_86] :
      ( k1_relset_1(A_84,B_85,C_86) = k1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_83,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_79])).

tff(c_164,plain,(
    ! [B_105,A_106,C_107] :
      ( k1_xboole_0 = B_105
      | k1_relset_1(A_106,B_105,C_107) = A_106
      | ~ v1_funct_2(C_107,A_106,B_105)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_171,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_164])).

tff(c_175,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_83,c_171])).

tff(c_176,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_271,plain,(
    ! [A_138,B_139,D_140] :
      ( r2_hidden('#skF_4'(A_138,B_139,k9_relat_1(A_138,B_139),D_140),k1_relat_1(A_138))
      | ~ r2_hidden(D_140,k9_relat_1(A_138,B_139))
      | ~ v1_funct_1(A_138)
      | ~ v1_relat_1(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_282,plain,(
    ! [B_139,D_140] :
      ( r2_hidden('#skF_4'('#skF_8',B_139,k9_relat_1('#skF_8',B_139),D_140),'#skF_5')
      | ~ r2_hidden(D_140,k9_relat_1('#skF_8',B_139))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_271])).

tff(c_303,plain,(
    ! [B_144,D_145] :
      ( r2_hidden('#skF_4'('#skF_8',B_144,k9_relat_1('#skF_8',B_144),D_145),'#skF_5')
      | ~ r2_hidden(D_145,k9_relat_1('#skF_8',B_144)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_60,c_282])).

tff(c_211,plain,(
    ! [A_119,B_120,D_121] :
      ( r2_hidden('#skF_4'(A_119,B_120,k9_relat_1(A_119,B_120),D_121),B_120)
      | ~ r2_hidden(D_121,k9_relat_1(A_119,B_120))
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    ! [F_71] :
      ( k1_funct_1('#skF_8',F_71) != '#skF_9'
      | ~ r2_hidden(F_71,'#skF_7')
      | ~ r2_hidden(F_71,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_222,plain,(
    ! [A_119,D_121] :
      ( k1_funct_1('#skF_8','#skF_4'(A_119,'#skF_7',k9_relat_1(A_119,'#skF_7'),D_121)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_119,'#skF_7',k9_relat_1(A_119,'#skF_7'),D_121),'#skF_5')
      | ~ r2_hidden(D_121,k9_relat_1(A_119,'#skF_7'))
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(resolution,[status(thm)],[c_211,c_52])).

tff(c_307,plain,(
    ! [D_145] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_145)) != '#skF_9'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_145,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_303,c_222])).

tff(c_319,plain,(
    ! [D_148] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_148)) != '#skF_9'
      | ~ r2_hidden(D_148,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_60,c_307])).

tff(c_323,plain,(
    ! [D_44] :
      ( D_44 != '#skF_9'
      | ~ r2_hidden(D_44,k9_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_44,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_319])).

tff(c_326,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_60,c_323])).

tff(c_89,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k7_relset_1(A_89,B_90,C_91,D_92) = k9_relat_1(C_91,D_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_92,plain,(
    ! [D_92] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_92) = k9_relat_1('#skF_8',D_92) ),
    inference(resolution,[status(thm)],[c_56,c_89])).

tff(c_54,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_95,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_54])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_326,c_95])).

tff(c_329,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_336,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_2])).

tff(c_113,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( m1_subset_1(k7_relset_1(A_95,B_96,C_97,D_98),k1_zfmisc_1(B_96))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_131,plain,(
    ! [D_92] :
      ( m1_subset_1(k9_relat_1('#skF_8',D_92),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_113])).

tff(c_138,plain,(
    ! [D_99] : m1_subset_1(k9_relat_1('#skF_8',D_99),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_131])).

tff(c_73,plain,(
    ! [C_79,A_80,B_81] :
      ( r2_hidden(C_79,A_80)
      | ~ r2_hidden(C_79,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [A_80] :
      ( r2_hidden('#skF_9',A_80)
      | ~ m1_subset_1(k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7'),k1_zfmisc_1(A_80)) ) ),
    inference(resolution,[status(thm)],[c_54,c_73])).

tff(c_93,plain,(
    ! [A_80] :
      ( r2_hidden('#skF_9',A_80)
      | ~ m1_subset_1(k9_relat_1('#skF_8','#skF_7'),k1_zfmisc_1(A_80)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_76])).

tff(c_143,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_138,c_93])).

tff(c_30,plain,(
    ! [B_49,A_48] :
      ( ~ r1_tarski(B_49,A_48)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_150,plain,(
    ~ r1_tarski('#skF_6','#skF_9') ),
    inference(resolution,[status(thm)],[c_143,c_30])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.38  
% 2.52/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.38  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.52/1.38  
% 2.52/1.38  %Foreground sorts:
% 2.52/1.38  
% 2.52/1.38  
% 2.52/1.38  %Background operators:
% 2.52/1.38  
% 2.52/1.38  
% 2.52/1.38  %Foreground operators:
% 2.52/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.52/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.52/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.52/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.38  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.52/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.52/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.52/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.52/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.52/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.52/1.38  tff('#skF_9', type, '#skF_9': $i).
% 2.52/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.52/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.52/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.52/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.52/1.38  tff('#skF_8', type, '#skF_8': $i).
% 2.52/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.52/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.52/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.52/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.52/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.52/1.38  
% 2.52/1.39  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 2.52/1.39  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.52/1.39  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 2.52/1.39  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.52/1.39  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.52/1.39  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.52/1.39  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.52/1.39  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 2.52/1.39  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.52/1.39  tff(f_56, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.52/1.39  tff(c_56, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.52/1.39  tff(c_67, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.52/1.39  tff(c_71, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_67])).
% 2.52/1.39  tff(c_60, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.52/1.39  tff(c_8, plain, (![A_6, B_29, D_44]: (k1_funct_1(A_6, '#skF_4'(A_6, B_29, k9_relat_1(A_6, B_29), D_44))=D_44 | ~r2_hidden(D_44, k9_relat_1(A_6, B_29)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.52/1.39  tff(c_58, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.52/1.39  tff(c_79, plain, (![A_84, B_85, C_86]: (k1_relset_1(A_84, B_85, C_86)=k1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.52/1.39  tff(c_83, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_79])).
% 2.52/1.39  tff(c_164, plain, (![B_105, A_106, C_107]: (k1_xboole_0=B_105 | k1_relset_1(A_106, B_105, C_107)=A_106 | ~v1_funct_2(C_107, A_106, B_105) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.52/1.39  tff(c_171, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_164])).
% 2.52/1.39  tff(c_175, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_83, c_171])).
% 2.52/1.39  tff(c_176, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_175])).
% 2.52/1.39  tff(c_271, plain, (![A_138, B_139, D_140]: (r2_hidden('#skF_4'(A_138, B_139, k9_relat_1(A_138, B_139), D_140), k1_relat_1(A_138)) | ~r2_hidden(D_140, k9_relat_1(A_138, B_139)) | ~v1_funct_1(A_138) | ~v1_relat_1(A_138))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.52/1.39  tff(c_282, plain, (![B_139, D_140]: (r2_hidden('#skF_4'('#skF_8', B_139, k9_relat_1('#skF_8', B_139), D_140), '#skF_5') | ~r2_hidden(D_140, k9_relat_1('#skF_8', B_139)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_271])).
% 2.52/1.39  tff(c_303, plain, (![B_144, D_145]: (r2_hidden('#skF_4'('#skF_8', B_144, k9_relat_1('#skF_8', B_144), D_145), '#skF_5') | ~r2_hidden(D_145, k9_relat_1('#skF_8', B_144)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_60, c_282])).
% 2.52/1.39  tff(c_211, plain, (![A_119, B_120, D_121]: (r2_hidden('#skF_4'(A_119, B_120, k9_relat_1(A_119, B_120), D_121), B_120) | ~r2_hidden(D_121, k9_relat_1(A_119, B_120)) | ~v1_funct_1(A_119) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.52/1.39  tff(c_52, plain, (![F_71]: (k1_funct_1('#skF_8', F_71)!='#skF_9' | ~r2_hidden(F_71, '#skF_7') | ~r2_hidden(F_71, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.52/1.39  tff(c_222, plain, (![A_119, D_121]: (k1_funct_1('#skF_8', '#skF_4'(A_119, '#skF_7', k9_relat_1(A_119, '#skF_7'), D_121))!='#skF_9' | ~r2_hidden('#skF_4'(A_119, '#skF_7', k9_relat_1(A_119, '#skF_7'), D_121), '#skF_5') | ~r2_hidden(D_121, k9_relat_1(A_119, '#skF_7')) | ~v1_funct_1(A_119) | ~v1_relat_1(A_119))), inference(resolution, [status(thm)], [c_211, c_52])).
% 2.52/1.39  tff(c_307, plain, (![D_145]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_145))!='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_145, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_303, c_222])).
% 2.52/1.39  tff(c_319, plain, (![D_148]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_148))!='#skF_9' | ~r2_hidden(D_148, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_60, c_307])).
% 2.52/1.39  tff(c_323, plain, (![D_44]: (D_44!='#skF_9' | ~r2_hidden(D_44, k9_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_44, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_319])).
% 2.52/1.39  tff(c_326, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_60, c_323])).
% 2.52/1.39  tff(c_89, plain, (![A_89, B_90, C_91, D_92]: (k7_relset_1(A_89, B_90, C_91, D_92)=k9_relat_1(C_91, D_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.39  tff(c_92, plain, (![D_92]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_92)=k9_relat_1('#skF_8', D_92))), inference(resolution, [status(thm)], [c_56, c_89])).
% 2.52/1.39  tff(c_54, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.52/1.39  tff(c_95, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_54])).
% 2.52/1.39  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_326, c_95])).
% 2.52/1.39  tff(c_329, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_175])).
% 2.52/1.39  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.52/1.39  tff(c_336, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_2])).
% 2.52/1.39  tff(c_113, plain, (![A_95, B_96, C_97, D_98]: (m1_subset_1(k7_relset_1(A_95, B_96, C_97, D_98), k1_zfmisc_1(B_96)) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.52/1.39  tff(c_131, plain, (![D_92]: (m1_subset_1(k9_relat_1('#skF_8', D_92), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_92, c_113])).
% 2.52/1.39  tff(c_138, plain, (![D_99]: (m1_subset_1(k9_relat_1('#skF_8', D_99), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_131])).
% 2.52/1.39  tff(c_73, plain, (![C_79, A_80, B_81]: (r2_hidden(C_79, A_80) | ~r2_hidden(C_79, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.52/1.39  tff(c_76, plain, (![A_80]: (r2_hidden('#skF_9', A_80) | ~m1_subset_1(k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'), k1_zfmisc_1(A_80)))), inference(resolution, [status(thm)], [c_54, c_73])).
% 2.52/1.39  tff(c_93, plain, (![A_80]: (r2_hidden('#skF_9', A_80) | ~m1_subset_1(k9_relat_1('#skF_8', '#skF_7'), k1_zfmisc_1(A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_76])).
% 2.52/1.39  tff(c_143, plain, (r2_hidden('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_138, c_93])).
% 2.52/1.39  tff(c_30, plain, (![B_49, A_48]: (~r1_tarski(B_49, A_48) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.52/1.39  tff(c_150, plain, (~r1_tarski('#skF_6', '#skF_9')), inference(resolution, [status(thm)], [c_143, c_30])).
% 2.52/1.39  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_336, c_150])).
% 2.52/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.39  
% 2.52/1.39  Inference rules
% 2.52/1.39  ----------------------
% 2.52/1.39  #Ref     : 0
% 2.52/1.39  #Sup     : 57
% 2.52/1.40  #Fact    : 0
% 2.52/1.40  #Define  : 0
% 2.52/1.40  #Split   : 1
% 2.52/1.40  #Chain   : 0
% 2.52/1.40  #Close   : 0
% 2.52/1.40  
% 2.52/1.40  Ordering : KBO
% 2.52/1.40  
% 2.52/1.40  Simplification rules
% 2.52/1.40  ----------------------
% 2.52/1.40  #Subsume      : 4
% 2.52/1.40  #Demod        : 37
% 2.52/1.40  #Tautology    : 13
% 2.52/1.40  #SimpNegUnit  : 1
% 2.52/1.40  #BackRed      : 12
% 2.52/1.40  
% 2.52/1.40  #Partial instantiations: 0
% 2.52/1.40  #Strategies tried      : 1
% 2.52/1.40  
% 2.52/1.40  Timing (in seconds)
% 2.52/1.40  ----------------------
% 2.52/1.40  Preprocessing        : 0.35
% 2.52/1.40  Parsing              : 0.17
% 2.52/1.40  CNF conversion       : 0.03
% 2.52/1.40  Main loop            : 0.24
% 2.52/1.40  Inferencing          : 0.08
% 2.52/1.40  Reduction            : 0.07
% 2.52/1.40  Demodulation         : 0.05
% 2.52/1.40  BG Simplification    : 0.02
% 2.52/1.40  Subsumption          : 0.05
% 2.52/1.40  Abstraction          : 0.02
% 2.52/1.40  MUC search           : 0.00
% 2.52/1.40  Cooper               : 0.00
% 2.52/1.40  Total                : 0.62
% 2.52/1.40  Index Insertion      : 0.00
% 2.52/1.40  Index Deletion       : 0.00
% 2.52/1.40  Index Matching       : 0.00
% 2.52/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
