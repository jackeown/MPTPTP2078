%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:30 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 124 expanded)
%              Number of leaves         :   37 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 288 expanded)
%              Number of equality atoms :   27 (  66 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
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

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_52,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_69,plain,(
    ! [C_72,B_73,A_74] :
      ( v5_relat_1(C_72,B_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_73,plain,(
    v5_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_69])).

tff(c_64,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_68,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_64])).

tff(c_56,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6,plain,(
    ! [A_2,C_38] :
      ( k1_funct_1(A_2,'#skF_4'(A_2,k2_relat_1(A_2),C_38)) = C_38
      | ~ r2_hidden(C_38,k2_relat_1(A_2))
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_95,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_99,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_95])).

tff(c_215,plain,(
    ! [B_115,A_116,C_117] :
      ( k1_xboole_0 = B_115
      | k1_relset_1(A_116,B_115,C_117) = A_116
      | ~ v1_funct_2(C_117,A_116,B_115)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_218,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_215])).

tff(c_221,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_99,c_218])).

tff(c_222,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_8,plain,(
    ! [A_2,C_38] :
      ( r2_hidden('#skF_4'(A_2,k2_relat_1(A_2),C_38),k1_relat_1(A_2))
      | ~ r2_hidden(C_38,k2_relat_1(A_2))
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_236,plain,(
    ! [C_38] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_38),'#skF_5')
      | ~ r2_hidden(C_38,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_8])).

tff(c_253,plain,(
    ! [C_119] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_119),'#skF_5')
      | ~ r2_hidden(C_119,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_56,c_236])).

tff(c_48,plain,(
    ! [E_64] :
      ( k1_funct_1('#skF_8',E_64) != '#skF_7'
      | ~ r2_hidden(E_64,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_271,plain,(
    ! [C_124] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_124)) != '#skF_7'
      | ~ r2_hidden(C_124,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_253,c_48])).

tff(c_275,plain,(
    ! [C_38] :
      ( C_38 != '#skF_7'
      | ~ r2_hidden(C_38,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_38,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_271])).

tff(c_278,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_56,c_275])).

tff(c_79,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_83,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_79])).

tff(c_50,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_86,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_50])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_86])).

tff(c_281,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_118,plain,(
    ! [B_97,C_98,A_99] :
      ( r2_hidden(k1_funct_1(B_97,C_98),A_99)
      | ~ r2_hidden(C_98,k1_relat_1(B_97))
      | ~ v1_funct_1(B_97)
      | ~ v5_relat_1(B_97,A_99)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [B_47,A_46] :
      ( ~ r1_tarski(B_47,A_46)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_157,plain,(
    ! [A_106,B_107,C_108] :
      ( ~ r1_tarski(A_106,k1_funct_1(B_107,C_108))
      | ~ r2_hidden(C_108,k1_relat_1(B_107))
      | ~ v1_funct_1(B_107)
      | ~ v5_relat_1(B_107,A_106)
      | ~ v1_relat_1(B_107) ) ),
    inference(resolution,[status(thm)],[c_118,c_24])).

tff(c_164,plain,(
    ! [C_109,B_110] :
      ( ~ r2_hidden(C_109,k1_relat_1(B_110))
      | ~ v1_funct_1(B_110)
      | ~ v5_relat_1(B_110,k1_xboole_0)
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_2,c_157])).

tff(c_174,plain,(
    ! [A_111,C_112] :
      ( ~ v5_relat_1(A_111,k1_xboole_0)
      | ~ r2_hidden(C_112,k2_relat_1(A_111))
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(resolution,[status(thm)],[c_8,c_164])).

tff(c_184,plain,
    ( ~ v5_relat_1('#skF_8',k1_xboole_0)
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_86,c_174])).

tff(c_189,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_56,c_184])).

tff(c_285,plain,(
    ~ v5_relat_1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_189])).

tff(c_295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_285])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:20:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.39  
% 2.41/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.40  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.41/1.40  
% 2.41/1.40  %Foreground sorts:
% 2.41/1.40  
% 2.41/1.40  
% 2.41/1.40  %Background operators:
% 2.41/1.40  
% 2.41/1.40  
% 2.41/1.40  %Foreground operators:
% 2.41/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.41/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.41/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.41/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.41/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.41/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.41/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.41/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.41/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.41/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.41/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.41/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.41/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.41/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.41/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.41/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.41/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.41/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.41/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.41/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.40  
% 2.41/1.41  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 2.41/1.41  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.41/1.41  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.41/1.41  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.41/1.41  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.41/1.41  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.41/1.41  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.41/1.41  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.41/1.41  tff(f_53, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 2.41/1.41  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.41/1.41  tff(c_52, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.41/1.41  tff(c_69, plain, (![C_72, B_73, A_74]: (v5_relat_1(C_72, B_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.41/1.41  tff(c_73, plain, (v5_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_69])).
% 2.41/1.41  tff(c_64, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.41/1.41  tff(c_68, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_52, c_64])).
% 2.41/1.41  tff(c_56, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.41/1.41  tff(c_6, plain, (![A_2, C_38]: (k1_funct_1(A_2, '#skF_4'(A_2, k2_relat_1(A_2), C_38))=C_38 | ~r2_hidden(C_38, k2_relat_1(A_2)) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.41/1.41  tff(c_54, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.41/1.41  tff(c_95, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.41/1.41  tff(c_99, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_52, c_95])).
% 2.41/1.41  tff(c_215, plain, (![B_115, A_116, C_117]: (k1_xboole_0=B_115 | k1_relset_1(A_116, B_115, C_117)=A_116 | ~v1_funct_2(C_117, A_116, B_115) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.41/1.41  tff(c_218, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_215])).
% 2.41/1.41  tff(c_221, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_99, c_218])).
% 2.41/1.41  tff(c_222, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_221])).
% 2.41/1.41  tff(c_8, plain, (![A_2, C_38]: (r2_hidden('#skF_4'(A_2, k2_relat_1(A_2), C_38), k1_relat_1(A_2)) | ~r2_hidden(C_38, k2_relat_1(A_2)) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.41/1.41  tff(c_236, plain, (![C_38]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_38), '#skF_5') | ~r2_hidden(C_38, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_8])).
% 2.41/1.41  tff(c_253, plain, (![C_119]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_119), '#skF_5') | ~r2_hidden(C_119, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_56, c_236])).
% 2.41/1.41  tff(c_48, plain, (![E_64]: (k1_funct_1('#skF_8', E_64)!='#skF_7' | ~r2_hidden(E_64, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.41/1.41  tff(c_271, plain, (![C_124]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_124))!='#skF_7' | ~r2_hidden(C_124, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_253, c_48])).
% 2.41/1.41  tff(c_275, plain, (![C_38]: (C_38!='#skF_7' | ~r2_hidden(C_38, k2_relat_1('#skF_8')) | ~r2_hidden(C_38, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_271])).
% 2.41/1.41  tff(c_278, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_56, c_275])).
% 2.41/1.41  tff(c_79, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.41/1.41  tff(c_83, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_52, c_79])).
% 2.41/1.41  tff(c_50, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.41/1.41  tff(c_86, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_50])).
% 2.41/1.41  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_278, c_86])).
% 2.41/1.41  tff(c_281, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_221])).
% 2.41/1.41  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.41/1.41  tff(c_118, plain, (![B_97, C_98, A_99]: (r2_hidden(k1_funct_1(B_97, C_98), A_99) | ~r2_hidden(C_98, k1_relat_1(B_97)) | ~v1_funct_1(B_97) | ~v5_relat_1(B_97, A_99) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.41/1.41  tff(c_24, plain, (![B_47, A_46]: (~r1_tarski(B_47, A_46) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.41/1.41  tff(c_157, plain, (![A_106, B_107, C_108]: (~r1_tarski(A_106, k1_funct_1(B_107, C_108)) | ~r2_hidden(C_108, k1_relat_1(B_107)) | ~v1_funct_1(B_107) | ~v5_relat_1(B_107, A_106) | ~v1_relat_1(B_107))), inference(resolution, [status(thm)], [c_118, c_24])).
% 2.41/1.41  tff(c_164, plain, (![C_109, B_110]: (~r2_hidden(C_109, k1_relat_1(B_110)) | ~v1_funct_1(B_110) | ~v5_relat_1(B_110, k1_xboole_0) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_2, c_157])).
% 2.41/1.41  tff(c_174, plain, (![A_111, C_112]: (~v5_relat_1(A_111, k1_xboole_0) | ~r2_hidden(C_112, k2_relat_1(A_111)) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(resolution, [status(thm)], [c_8, c_164])).
% 2.41/1.41  tff(c_184, plain, (~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_86, c_174])).
% 2.41/1.41  tff(c_189, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_56, c_184])).
% 2.41/1.41  tff(c_285, plain, (~v5_relat_1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_189])).
% 2.41/1.41  tff(c_295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_285])).
% 2.41/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.41  
% 2.41/1.41  Inference rules
% 2.41/1.41  ----------------------
% 2.41/1.41  #Ref     : 0
% 2.41/1.41  #Sup     : 47
% 2.41/1.41  #Fact    : 0
% 2.41/1.41  #Define  : 0
% 2.41/1.41  #Split   : 2
% 2.41/1.41  #Chain   : 0
% 2.41/1.41  #Close   : 0
% 2.41/1.41  
% 2.41/1.41  Ordering : KBO
% 2.41/1.41  
% 2.41/1.41  Simplification rules
% 2.41/1.41  ----------------------
% 2.41/1.41  #Subsume      : 7
% 2.41/1.41  #Demod        : 42
% 2.41/1.41  #Tautology    : 12
% 2.41/1.41  #SimpNegUnit  : 1
% 2.41/1.41  #BackRed      : 13
% 2.41/1.41  
% 2.41/1.41  #Partial instantiations: 0
% 2.41/1.41  #Strategies tried      : 1
% 2.41/1.41  
% 2.41/1.41  Timing (in seconds)
% 2.41/1.41  ----------------------
% 2.41/1.41  Preprocessing        : 0.35
% 2.41/1.41  Parsing              : 0.18
% 2.41/1.41  CNF conversion       : 0.03
% 2.41/1.41  Main loop            : 0.24
% 2.41/1.41  Inferencing          : 0.09
% 2.41/1.41  Reduction            : 0.07
% 2.41/1.41  Demodulation         : 0.05
% 2.41/1.41  BG Simplification    : 0.02
% 2.41/1.41  Subsumption          : 0.05
% 2.41/1.41  Abstraction          : 0.02
% 2.41/1.41  MUC search           : 0.00
% 2.41/1.41  Cooper               : 0.00
% 2.41/1.41  Total                : 0.62
% 2.41/1.41  Index Insertion      : 0.00
% 2.41/1.41  Index Deletion       : 0.00
% 2.41/1.41  Index Matching       : 0.00
% 2.41/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
