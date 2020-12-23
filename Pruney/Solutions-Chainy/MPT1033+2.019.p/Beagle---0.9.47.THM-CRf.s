%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:53 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 157 expanded)
%              Number of leaves         :   30 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :  153 ( 527 expanded)
%              Number of equality atoms :   11 (  67 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_121,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_98,axiom,(
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

tff(f_47,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_subset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

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

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_97,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( r2_relset_1(A_49,B_50,C_51,C_51)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_118,plain,(
    ! [C_57] :
      ( r2_relset_1('#skF_3','#skF_4',C_57,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_42,c_97])).

tff(c_130,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_118])).

tff(c_82,plain,(
    ! [C_46,B_47,A_48] :
      ( v1_xboole_0(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(B_47,A_48)))
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_94,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_82])).

tff(c_96,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_44,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_144,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_partfun1(C_65,A_66)
      | ~ v1_funct_2(C_65,A_66,B_67)
      | ~ v1_funct_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | v1_xboole_0(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_151,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_144])).

tff(c_158,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_151])).

tff(c_159,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_158])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_38,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_154,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_144])).

tff(c_162,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_154])).

tff(c_163,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_162])).

tff(c_34,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_179,plain,(
    ! [D_71,C_72,A_73,B_74] :
      ( D_71 = C_72
      | ~ r1_partfun1(C_72,D_71)
      | ~ v1_partfun1(D_71,A_73)
      | ~ v1_partfun1(C_72,A_73)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ v1_funct_1(D_71)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ v1_funct_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_181,plain,(
    ! [A_73,B_74] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_73)
      | ~ v1_partfun1('#skF_5',A_73)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_179])).

tff(c_184,plain,(
    ! [A_73,B_74] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_73)
      | ~ v1_partfun1('#skF_5',A_73)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_181])).

tff(c_187,plain,(
    ! [A_77,B_78] :
      ( ~ v1_partfun1('#skF_6',A_77)
      | ~ v1_partfun1('#skF_5',A_77)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_190,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_42,c_187])).

tff(c_194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_159,c_163,c_190])).

tff(c_195,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_30,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_199,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_30])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_199])).

tff(c_210,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_16,plain,(
    ! [A_8] :
      ( m1_subset_1('#skF_2'(A_8),k1_zfmisc_1(A_8))
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_246,plain,(
    ! [B_87,A_88] :
      ( v1_xboole_0('#skF_2'(k2_zfmisc_1(B_87,A_88)))
      | ~ v1_xboole_0(A_88)
      | v1_xboole_0(k2_zfmisc_1(B_87,A_88)) ) ),
    inference(resolution,[status(thm)],[c_16,c_82])).

tff(c_14,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0('#skF_2'(A_8))
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_251,plain,(
    ! [A_89,B_90] :
      ( ~ v1_xboole_0(A_89)
      | v1_xboole_0(k2_zfmisc_1(B_90,A_89)) ) ),
    inference(resolution,[status(thm)],[c_246,c_14])).

tff(c_67,plain,(
    ! [C_40,B_41,A_42] :
      ( ~ v1_xboole_0(C_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_42,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_67])).

tff(c_77,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_254,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_251,c_77])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_254])).

tff(c_260,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_76,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_42,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_67])).

tff(c_277,plain,(
    ! [A_96] : ~ r2_hidden(A_96,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_76])).

tff(c_282,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_277])).

tff(c_265,plain,(
    ! [A_94] : ~ r2_hidden(A_94,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_271,plain,(
    ! [B_95] : r1_tarski('#skF_5',B_95) ),
    inference(resolution,[status(thm)],[c_6,c_265])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_287,plain,(
    ! [B_98] :
      ( B_98 = '#skF_5'
      | ~ r1_tarski(B_98,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_271,c_8])).

tff(c_300,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_282,c_287])).

tff(c_309,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_30])).

tff(c_396,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( r2_relset_1(A_119,B_120,C_121,C_121)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_404,plain,(
    ! [C_123] :
      ( r2_relset_1('#skF_3','#skF_4',C_123,C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_396])).

tff(c_409,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_404])).

tff(c_415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:24:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.32  
% 2.26/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.32  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.26/1.32  
% 2.26/1.32  %Foreground sorts:
% 2.26/1.32  
% 2.26/1.32  
% 2.26/1.32  %Background operators:
% 2.26/1.32  
% 2.26/1.32  
% 2.26/1.32  %Foreground operators:
% 2.26/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.26/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.32  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.26/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.26/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.26/1.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.26/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.26/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.26/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.32  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.26/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.32  
% 2.68/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.68/1.34  tff(f_121, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 2.68/1.34  tff(f_67, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.68/1.34  tff(f_61, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.68/1.34  tff(f_81, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.68/1.34  tff(f_98, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 2.68/1.34  tff(f_47, axiom, (![A]: (~v1_xboole_0(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_subset_1)).
% 2.68/1.34  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.68/1.34  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.68/1.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.34  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.68/1.34  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.68/1.34  tff(c_97, plain, (![A_49, B_50, C_51, D_52]: (r2_relset_1(A_49, B_50, C_51, C_51) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.68/1.34  tff(c_118, plain, (![C_57]: (r2_relset_1('#skF_3', '#skF_4', C_57, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_42, c_97])).
% 2.68/1.34  tff(c_130, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_36, c_118])).
% 2.68/1.34  tff(c_82, plain, (![C_46, B_47, A_48]: (v1_xboole_0(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(B_47, A_48))) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.34  tff(c_94, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_82])).
% 2.68/1.34  tff(c_96, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_94])).
% 2.68/1.34  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.68/1.34  tff(c_44, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.68/1.34  tff(c_144, plain, (![C_65, A_66, B_67]: (v1_partfun1(C_65, A_66) | ~v1_funct_2(C_65, A_66, B_67) | ~v1_funct_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | v1_xboole_0(B_67))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.68/1.34  tff(c_151, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_144])).
% 2.68/1.34  tff(c_158, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_151])).
% 2.68/1.34  tff(c_159, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_96, c_158])).
% 2.68/1.34  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.68/1.34  tff(c_38, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.68/1.34  tff(c_154, plain, (v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_144])).
% 2.68/1.34  tff(c_162, plain, (v1_partfun1('#skF_6', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_154])).
% 2.68/1.34  tff(c_163, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_96, c_162])).
% 2.68/1.34  tff(c_34, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.68/1.34  tff(c_179, plain, (![D_71, C_72, A_73, B_74]: (D_71=C_72 | ~r1_partfun1(C_72, D_71) | ~v1_partfun1(D_71, A_73) | ~v1_partfun1(C_72, A_73) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~v1_funct_1(D_71) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~v1_funct_1(C_72))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.34  tff(c_181, plain, (![A_73, B_74]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_73) | ~v1_partfun1('#skF_5', A_73) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_179])).
% 2.68/1.34  tff(c_184, plain, (![A_73, B_74]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_73) | ~v1_partfun1('#skF_5', A_73) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_181])).
% 2.68/1.34  tff(c_187, plain, (![A_77, B_78]: (~v1_partfun1('#skF_6', A_77) | ~v1_partfun1('#skF_5', A_77) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(splitLeft, [status(thm)], [c_184])).
% 2.68/1.34  tff(c_190, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_42, c_187])).
% 2.68/1.34  tff(c_194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_159, c_163, c_190])).
% 2.68/1.34  tff(c_195, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_184])).
% 2.68/1.34  tff(c_30, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.68/1.34  tff(c_199, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_30])).
% 2.68/1.34  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_199])).
% 2.68/1.34  tff(c_210, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_94])).
% 2.68/1.34  tff(c_16, plain, (![A_8]: (m1_subset_1('#skF_2'(A_8), k1_zfmisc_1(A_8)) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.68/1.34  tff(c_246, plain, (![B_87, A_88]: (v1_xboole_0('#skF_2'(k2_zfmisc_1(B_87, A_88))) | ~v1_xboole_0(A_88) | v1_xboole_0(k2_zfmisc_1(B_87, A_88)))), inference(resolution, [status(thm)], [c_16, c_82])).
% 2.68/1.34  tff(c_14, plain, (![A_8]: (~v1_xboole_0('#skF_2'(A_8)) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.68/1.34  tff(c_251, plain, (![A_89, B_90]: (~v1_xboole_0(A_89) | v1_xboole_0(k2_zfmisc_1(B_90, A_89)))), inference(resolution, [status(thm)], [c_246, c_14])).
% 2.68/1.34  tff(c_67, plain, (![C_40, B_41, A_42]: (~v1_xboole_0(C_40) | ~m1_subset_1(B_41, k1_zfmisc_1(C_40)) | ~r2_hidden(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.68/1.34  tff(c_75, plain, (![A_42]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_42, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_67])).
% 2.68/1.34  tff(c_77, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_75])).
% 2.68/1.34  tff(c_254, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_251, c_77])).
% 2.68/1.34  tff(c_258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_254])).
% 2.68/1.34  tff(c_260, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_75])).
% 2.68/1.34  tff(c_76, plain, (![A_42]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_42, '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_67])).
% 2.68/1.34  tff(c_277, plain, (![A_96]: (~r2_hidden(A_96, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_76])).
% 2.68/1.34  tff(c_282, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_277])).
% 2.68/1.34  tff(c_265, plain, (![A_94]: (~r2_hidden(A_94, '#skF_5'))), inference(splitRight, [status(thm)], [c_75])).
% 2.68/1.34  tff(c_271, plain, (![B_95]: (r1_tarski('#skF_5', B_95))), inference(resolution, [status(thm)], [c_6, c_265])).
% 2.68/1.34  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.68/1.34  tff(c_287, plain, (![B_98]: (B_98='#skF_5' | ~r1_tarski(B_98, '#skF_5'))), inference(resolution, [status(thm)], [c_271, c_8])).
% 2.68/1.34  tff(c_300, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_282, c_287])).
% 2.68/1.34  tff(c_309, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_30])).
% 2.68/1.34  tff(c_396, plain, (![A_119, B_120, C_121, D_122]: (r2_relset_1(A_119, B_120, C_121, C_121) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.68/1.34  tff(c_404, plain, (![C_123]: (r2_relset_1('#skF_3', '#skF_4', C_123, C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_36, c_396])).
% 2.68/1.34  tff(c_409, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_36, c_404])).
% 2.68/1.34  tff(c_415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_309, c_409])).
% 2.68/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.34  
% 2.68/1.34  Inference rules
% 2.68/1.34  ----------------------
% 2.68/1.34  #Ref     : 0
% 2.68/1.34  #Sup     : 66
% 2.68/1.34  #Fact    : 0
% 2.68/1.34  #Define  : 0
% 2.68/1.34  #Split   : 5
% 2.68/1.34  #Chain   : 0
% 2.68/1.34  #Close   : 0
% 2.68/1.34  
% 2.68/1.34  Ordering : KBO
% 2.68/1.34  
% 2.68/1.34  Simplification rules
% 2.68/1.34  ----------------------
% 2.68/1.34  #Subsume      : 13
% 2.68/1.34  #Demod        : 47
% 2.68/1.34  #Tautology    : 26
% 2.68/1.34  #SimpNegUnit  : 8
% 2.68/1.34  #BackRed      : 15
% 2.68/1.34  
% 2.68/1.34  #Partial instantiations: 0
% 2.68/1.34  #Strategies tried      : 1
% 2.68/1.34  
% 2.68/1.34  Timing (in seconds)
% 2.68/1.34  ----------------------
% 2.68/1.34  Preprocessing        : 0.32
% 2.68/1.34  Parsing              : 0.17
% 2.68/1.34  CNF conversion       : 0.02
% 2.68/1.34  Main loop            : 0.27
% 2.68/1.34  Inferencing          : 0.10
% 2.68/1.34  Reduction            : 0.08
% 2.68/1.34  Demodulation         : 0.05
% 2.68/1.34  BG Simplification    : 0.01
% 2.68/1.34  Subsumption          : 0.05
% 2.68/1.34  Abstraction          : 0.01
% 2.68/1.34  MUC search           : 0.00
% 2.68/1.34  Cooper               : 0.00
% 2.68/1.34  Total                : 0.62
% 2.68/1.34  Index Insertion      : 0.00
% 2.68/1.34  Index Deletion       : 0.00
% 2.68/1.34  Index Matching       : 0.00
% 2.68/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
