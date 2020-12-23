%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:54 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 213 expanded)
%              Number of leaves         :   33 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 661 expanded)
%              Number of equality atoms :   14 (  81 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_80,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_partfun1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    ! [A_21,B_22] : m1_subset_1('#skF_2'(A_21,B_22),k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_120,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( r2_relset_1(A_64,B_65,C_66,C_66)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_130,plain,(
    ! [A_68,B_69,C_70] :
      ( r2_relset_1(A_68,B_69,C_70,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(resolution,[status(thm)],[c_32,c_120])).

tff(c_139,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_130])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | ~ v1_xboole_0(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_77,plain,(
    ! [C_49,B_50,A_51] :
      ( ~ v1_xboole_0(C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_85,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_51,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_77])).

tff(c_87,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_91,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_87])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_141,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_partfun1(C_73,A_74)
      | ~ v1_funct_2(C_73,A_74,B_75)
      | ~ v1_funct_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | v1_xboole_0(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_147,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_141])).

tff(c_156,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_147])).

tff(c_157,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_156])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_150,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_141])).

tff(c_160,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_150])).

tff(c_161,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_160])).

tff(c_40,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_162,plain,(
    ! [D_76,C_77,A_78,B_79] :
      ( D_76 = C_77
      | ~ r1_partfun1(C_77,D_76)
      | ~ v1_partfun1(D_76,A_78)
      | ~ v1_partfun1(C_77,A_78)
      | ~ m1_subset_1(D_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_1(D_76)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_164,plain,(
    ! [A_78,B_79] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_78)
      | ~ v1_partfun1('#skF_5',A_78)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_162])).

tff(c_167,plain,(
    ! [A_78,B_79] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_78)
      | ~ v1_partfun1('#skF_5',A_78)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_164])).

tff(c_214,plain,(
    ! [A_110,B_111] :
      ( ~ v1_partfun1('#skF_6',A_110)
      | ~ v1_partfun1('#skF_5',A_110)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_217,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_48,c_214])).

tff(c_221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_157,c_161,c_217])).

tff(c_222,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_36,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_226,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_36])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_226])).

tff(c_237,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_86,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_51,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_77])).

tff(c_267,plain,(
    ! [A_118] : ~ r2_hidden(A_118,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_86])).

tff(c_273,plain,(
    ! [B_119] : r1_tarski('#skF_6',B_119) ),
    inference(resolution,[status(thm)],[c_6,c_267])).

tff(c_238,plain,(
    ! [A_112] : ~ r2_hidden(A_112,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_244,plain,(
    ! [B_113] : r1_tarski('#skF_5',B_113) ),
    inference(resolution,[status(thm)],[c_6,c_238])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_247,plain,(
    ! [B_113] :
      ( B_113 = '#skF_5'
      | ~ r1_tarski(B_113,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_244,c_8])).

tff(c_280,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_273,c_247])).

tff(c_286,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_36])).

tff(c_311,plain,(
    ! [A_121,B_122,A_123] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_121,B_122))
      | ~ r2_hidden(A_123,'#skF_2'(A_121,B_122)) ) ),
    inference(resolution,[status(thm)],[c_32,c_77])).

tff(c_317,plain,(
    ! [A_124,B_125,B_126] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_124,B_125))
      | r1_tarski('#skF_2'(A_124,B_125),B_126) ) ),
    inference(resolution,[status(thm)],[c_6,c_311])).

tff(c_281,plain,(
    ! [B_119] :
      ( B_119 = '#skF_6'
      | ~ r1_tarski(B_119,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_273,c_8])).

tff(c_333,plain,(
    ! [A_131,B_132] :
      ( '#skF_2'(A_131,B_132) = '#skF_6'
      | ~ v1_xboole_0(k2_zfmisc_1(A_131,B_132)) ) ),
    inference(resolution,[status(thm)],[c_317,c_281])).

tff(c_340,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_237,c_333])).

tff(c_326,plain,(
    ! [A_127,B_128,C_129,D_130] :
      ( r2_relset_1(A_127,B_128,C_129,C_129)
      | ~ m1_subset_1(D_130,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_371,plain,(
    ! [C_133] :
      ( r2_relset_1('#skF_3','#skF_4',C_133,C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_42,c_326])).

tff(c_374,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4'),'#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_371])).

tff(c_378,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_340,c_374])).

tff(c_380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_286,c_378])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.42  
% 2.57/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.42  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.57/1.42  
% 2.57/1.42  %Foreground sorts:
% 2.57/1.42  
% 2.57/1.42  
% 2.57/1.42  %Background operators:
% 2.57/1.42  
% 2.57/1.42  
% 2.57/1.42  %Foreground operators:
% 2.57/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.57/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.42  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.57/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.57/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.57/1.42  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.57/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.57/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.57/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.57/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.57/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.57/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.57/1.42  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.57/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.42  
% 2.57/1.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.57/1.44  tff(f_120, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 2.57/1.44  tff(f_80, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_partfun1)).
% 2.57/1.44  tff(f_55, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.57/1.44  tff(f_42, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.57/1.44  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.57/1.44  tff(f_69, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.57/1.44  tff(f_97, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 2.57/1.44  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.57/1.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.57/1.44  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.57/1.44  tff(c_32, plain, (![A_21, B_22]: (m1_subset_1('#skF_2'(A_21, B_22), k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.44  tff(c_120, plain, (![A_64, B_65, C_66, D_67]: (r2_relset_1(A_64, B_65, C_66, C_66) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.57/1.44  tff(c_130, plain, (![A_68, B_69, C_70]: (r2_relset_1(A_68, B_69, C_70, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(resolution, [status(thm)], [c_32, c_120])).
% 2.57/1.44  tff(c_139, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_130])).
% 2.57/1.44  tff(c_14, plain, (![A_8, B_9]: (v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | ~v1_xboole_0(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.57/1.44  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.57/1.44  tff(c_77, plain, (![C_49, B_50, A_51]: (~v1_xboole_0(C_49) | ~m1_subset_1(B_50, k1_zfmisc_1(C_49)) | ~r2_hidden(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.57/1.44  tff(c_85, plain, (![A_51]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_51, '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_77])).
% 2.57/1.44  tff(c_87, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_85])).
% 2.57/1.44  tff(c_91, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_14, c_87])).
% 2.57/1.44  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.57/1.44  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.57/1.44  tff(c_141, plain, (![C_73, A_74, B_75]: (v1_partfun1(C_73, A_74) | ~v1_funct_2(C_73, A_74, B_75) | ~v1_funct_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | v1_xboole_0(B_75))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.57/1.44  tff(c_147, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_141])).
% 2.57/1.44  tff(c_156, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_147])).
% 2.57/1.44  tff(c_157, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_91, c_156])).
% 2.57/1.44  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.57/1.44  tff(c_44, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.57/1.44  tff(c_150, plain, (v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_141])).
% 2.57/1.44  tff(c_160, plain, (v1_partfun1('#skF_6', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_150])).
% 2.57/1.44  tff(c_161, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_91, c_160])).
% 2.57/1.44  tff(c_40, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.57/1.44  tff(c_162, plain, (![D_76, C_77, A_78, B_79]: (D_76=C_77 | ~r1_partfun1(C_77, D_76) | ~v1_partfun1(D_76, A_78) | ~v1_partfun1(C_77, A_78) | ~m1_subset_1(D_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_1(D_76) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_1(C_77))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.57/1.44  tff(c_164, plain, (![A_78, B_79]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_78) | ~v1_partfun1('#skF_5', A_78) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_162])).
% 2.57/1.44  tff(c_167, plain, (![A_78, B_79]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_78) | ~v1_partfun1('#skF_5', A_78) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_164])).
% 2.57/1.44  tff(c_214, plain, (![A_110, B_111]: (~v1_partfun1('#skF_6', A_110) | ~v1_partfun1('#skF_5', A_110) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(splitLeft, [status(thm)], [c_167])).
% 2.57/1.44  tff(c_217, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_48, c_214])).
% 2.57/1.44  tff(c_221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_157, c_161, c_217])).
% 2.57/1.44  tff(c_222, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_167])).
% 2.57/1.44  tff(c_36, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.57/1.44  tff(c_226, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_36])).
% 2.57/1.44  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_226])).
% 2.57/1.44  tff(c_237, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_85])).
% 2.57/1.44  tff(c_86, plain, (![A_51]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_51, '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_77])).
% 2.57/1.44  tff(c_267, plain, (![A_118]: (~r2_hidden(A_118, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_86])).
% 2.57/1.44  tff(c_273, plain, (![B_119]: (r1_tarski('#skF_6', B_119))), inference(resolution, [status(thm)], [c_6, c_267])).
% 2.57/1.44  tff(c_238, plain, (![A_112]: (~r2_hidden(A_112, '#skF_5'))), inference(splitRight, [status(thm)], [c_85])).
% 2.57/1.44  tff(c_244, plain, (![B_113]: (r1_tarski('#skF_5', B_113))), inference(resolution, [status(thm)], [c_6, c_238])).
% 2.57/1.44  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.57/1.44  tff(c_247, plain, (![B_113]: (B_113='#skF_5' | ~r1_tarski(B_113, '#skF_5'))), inference(resolution, [status(thm)], [c_244, c_8])).
% 2.57/1.44  tff(c_280, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_273, c_247])).
% 2.57/1.44  tff(c_286, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_280, c_36])).
% 2.57/1.44  tff(c_311, plain, (![A_121, B_122, A_123]: (~v1_xboole_0(k2_zfmisc_1(A_121, B_122)) | ~r2_hidden(A_123, '#skF_2'(A_121, B_122)))), inference(resolution, [status(thm)], [c_32, c_77])).
% 2.57/1.44  tff(c_317, plain, (![A_124, B_125, B_126]: (~v1_xboole_0(k2_zfmisc_1(A_124, B_125)) | r1_tarski('#skF_2'(A_124, B_125), B_126))), inference(resolution, [status(thm)], [c_6, c_311])).
% 2.57/1.44  tff(c_281, plain, (![B_119]: (B_119='#skF_6' | ~r1_tarski(B_119, '#skF_6'))), inference(resolution, [status(thm)], [c_273, c_8])).
% 2.57/1.44  tff(c_333, plain, (![A_131, B_132]: ('#skF_2'(A_131, B_132)='#skF_6' | ~v1_xboole_0(k2_zfmisc_1(A_131, B_132)))), inference(resolution, [status(thm)], [c_317, c_281])).
% 2.57/1.44  tff(c_340, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_237, c_333])).
% 2.57/1.44  tff(c_326, plain, (![A_127, B_128, C_129, D_130]: (r2_relset_1(A_127, B_128, C_129, C_129) | ~m1_subset_1(D_130, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.57/1.44  tff(c_371, plain, (![C_133]: (r2_relset_1('#skF_3', '#skF_4', C_133, C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_42, c_326])).
% 2.57/1.44  tff(c_374, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4'), '#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_371])).
% 2.57/1.44  tff(c_378, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_340, c_340, c_374])).
% 2.57/1.44  tff(c_380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_286, c_378])).
% 2.57/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.44  
% 2.57/1.44  Inference rules
% 2.57/1.44  ----------------------
% 2.57/1.44  #Ref     : 0
% 2.57/1.44  #Sup     : 63
% 2.57/1.44  #Fact    : 0
% 2.57/1.44  #Define  : 0
% 2.57/1.44  #Split   : 3
% 2.57/1.44  #Chain   : 0
% 2.57/1.44  #Close   : 0
% 2.57/1.44  
% 2.57/1.44  Ordering : KBO
% 2.57/1.44  
% 2.57/1.44  Simplification rules
% 2.57/1.44  ----------------------
% 2.57/1.44  #Subsume      : 11
% 2.57/1.44  #Demod        : 46
% 2.57/1.44  #Tautology    : 24
% 2.57/1.44  #SimpNegUnit  : 3
% 2.57/1.44  #BackRed      : 15
% 2.57/1.44  
% 2.57/1.44  #Partial instantiations: 0
% 2.57/1.44  #Strategies tried      : 1
% 2.57/1.44  
% 2.57/1.44  Timing (in seconds)
% 2.57/1.44  ----------------------
% 2.57/1.44  Preprocessing        : 0.39
% 2.57/1.44  Parsing              : 0.20
% 2.57/1.44  CNF conversion       : 0.03
% 2.57/1.44  Main loop            : 0.26
% 2.57/1.44  Inferencing          : 0.09
% 2.57/1.44  Reduction            : 0.08
% 2.57/1.44  Demodulation         : 0.06
% 2.57/1.44  BG Simplification    : 0.02
% 2.57/1.44  Subsumption          : 0.05
% 2.57/1.44  Abstraction          : 0.01
% 2.57/1.44  MUC search           : 0.00
% 2.57/1.44  Cooper               : 0.00
% 2.57/1.44  Total                : 0.69
% 2.57/1.44  Index Insertion      : 0.00
% 2.57/1.44  Index Deletion       : 0.00
% 2.57/1.44  Index Matching       : 0.00
% 2.57/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
