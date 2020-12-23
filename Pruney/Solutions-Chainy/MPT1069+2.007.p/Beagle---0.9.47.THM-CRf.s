%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:46 EST 2020

% Result     : Theorem 4.93s
% Output     : CNFRefutation 5.25s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 413 expanded)
%              Number of leaves         :   47 ( 160 expanded)
%              Depth                    :   16
%              Number of atoms          :  302 (1431 expanded)
%              Number of equality atoms :   64 ( 299 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_216,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_160,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_191,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(k2_relset_1(A,B,D),C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_172,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_72,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_82,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_80,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_78,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_538,plain,(
    ! [A_170,B_171,C_172] :
      ( k1_relset_1(A_170,B_171,C_172) = k1_relat_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_556,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_538])).

tff(c_70,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_560,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_70])).

tff(c_76,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1187,plain,(
    ! [C_244,B_248,F_247,D_245,A_243,E_246] :
      ( k1_funct_1(k8_funct_2(B_248,C_244,A_243,D_245,E_246),F_247) = k1_funct_1(E_246,k1_funct_1(D_245,F_247))
      | k1_xboole_0 = B_248
      | ~ r1_tarski(k2_relset_1(B_248,C_244,D_245),k1_relset_1(C_244,A_243,E_246))
      | ~ m1_subset_1(F_247,B_248)
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(C_244,A_243)))
      | ~ v1_funct_1(E_246)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(B_248,C_244)))
      | ~ v1_funct_2(D_245,B_248,C_244)
      | ~ v1_funct_1(D_245)
      | v1_xboole_0(C_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1197,plain,(
    ! [B_248,D_245,F_247] :
      ( k1_funct_1(k8_funct_2(B_248,'#skF_4','#skF_2',D_245,'#skF_6'),F_247) = k1_funct_1('#skF_6',k1_funct_1(D_245,F_247))
      | k1_xboole_0 = B_248
      | ~ r1_tarski(k2_relset_1(B_248,'#skF_4',D_245),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_247,B_248)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(B_248,'#skF_4')))
      | ~ v1_funct_2(D_245,B_248,'#skF_4')
      | ~ v1_funct_1(D_245)
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_1187])).

tff(c_1204,plain,(
    ! [B_248,D_245,F_247] :
      ( k1_funct_1(k8_funct_2(B_248,'#skF_4','#skF_2',D_245,'#skF_6'),F_247) = k1_funct_1('#skF_6',k1_funct_1(D_245,F_247))
      | k1_xboole_0 = B_248
      | ~ r1_tarski(k2_relset_1(B_248,'#skF_4',D_245),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_247,B_248)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(B_248,'#skF_4')))
      | ~ v1_funct_2(D_245,B_248,'#skF_4')
      | ~ v1_funct_1(D_245)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1197])).

tff(c_1241,plain,(
    ! [B_252,D_253,F_254] :
      ( k1_funct_1(k8_funct_2(B_252,'#skF_4','#skF_2',D_253,'#skF_6'),F_254) = k1_funct_1('#skF_6',k1_funct_1(D_253,F_254))
      | k1_xboole_0 = B_252
      | ~ r1_tarski(k2_relset_1(B_252,'#skF_4',D_253),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_254,B_252)
      | ~ m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1(B_252,'#skF_4')))
      | ~ v1_funct_2(D_253,B_252,'#skF_4')
      | ~ v1_funct_1(D_253) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1204])).

tff(c_1243,plain,(
    ! [F_254] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_254) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_254))
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(F_254,'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_560,c_1241])).

tff(c_1246,plain,(
    ! [F_254] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_254) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_254))
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(F_254,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_1243])).

tff(c_1247,plain,(
    ! [F_254] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_254) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_254))
      | ~ m1_subset_1(F_254,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1246])).

tff(c_475,plain,(
    ! [C_154,B_155,A_156] :
      ( v5_relat_1(C_154,B_155)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_156,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_493,plain,(
    v5_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_475])).

tff(c_295,plain,(
    ! [C_121,A_122,B_123] :
      ( v1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_311,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_295])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_216,plain,(
    ! [A_106,B_107] :
      ( r2_hidden('#skF_1'(A_106,B_107),A_106)
      | r1_xboole_0(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_112,plain,(
    ! [A_82,B_83] : ~ r2_hidden(A_82,k2_zfmisc_1(A_82,B_83)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_118,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_112])).

tff(c_222,plain,(
    ! [B_108] : r1_xboole_0(k1_xboole_0,B_108) ),
    inference(resolution,[status(thm)],[c_216,c_118])).

tff(c_120,plain,(
    ! [A_85,B_86] :
      ( v1_xboole_0(k2_zfmisc_1(A_85,B_86))
      | ~ v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_132,plain,(
    ! [A_12] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_120])).

tff(c_135,plain,(
    ! [A_12] : ~ v1_xboole_0(A_12) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( ~ r1_xboole_0(B_9,A_8)
      | ~ r1_tarski(B_9,A_8)
      | v1_xboole_0(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_153,plain,(
    ! [B_9,A_8] :
      ( ~ r1_xboole_0(B_9,A_8)
      | ~ r1_tarski(B_9,A_8) ) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_12])).

tff(c_225,plain,(
    ! [B_108] : ~ r1_tarski(k1_xboole_0,B_108) ),
    inference(resolution,[status(thm)],[c_222,c_153])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_225])).

tff(c_230,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( v1_xboole_0(k2_zfmisc_1(A_10,B_11))
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_347,plain,(
    ! [B_131,A_132] :
      ( v1_xboole_0(B_131)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(A_132))
      | ~ v1_xboole_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_359,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_78,c_347])).

tff(c_383,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_359])).

tff(c_387,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_383])).

tff(c_1045,plain,(
    ! [B_230,D_231,A_232,C_233] :
      ( k1_xboole_0 = B_230
      | v1_funct_2(D_231,A_232,C_233)
      | ~ r1_tarski(k2_relset_1(A_232,B_230,D_231),C_233)
      | ~ m1_subset_1(D_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_230)))
      | ~ v1_funct_2(D_231,A_232,B_230)
      | ~ v1_funct_1(D_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1047,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3',k1_relat_1('#skF_6'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_560,c_1045])).

tff(c_1050,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_1047])).

tff(c_1051,plain,(
    v1_funct_2('#skF_5','#skF_3',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1050])).

tff(c_1110,plain,(
    ! [B_239,D_240,A_241,C_242] :
      ( k1_xboole_0 = B_239
      | m1_subset_1(D_240,k1_zfmisc_1(k2_zfmisc_1(A_241,C_242)))
      | ~ r1_tarski(k2_relset_1(A_241,B_239,D_240),C_242)
      | ~ m1_subset_1(D_240,k1_zfmisc_1(k2_zfmisc_1(A_241,B_239)))
      | ~ v1_funct_2(D_240,A_241,B_239)
      | ~ v1_funct_1(D_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1112,plain,
    ( k1_xboole_0 = '#skF_4'
    | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_6'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_560,c_1110])).

tff(c_1115,plain,
    ( k1_xboole_0 = '#skF_4'
    | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_1112])).

tff(c_1116,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_1115])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_842,plain,(
    ! [D_210,C_211,B_212,A_213] :
      ( r2_hidden(k1_funct_1(D_210,C_211),B_212)
      | k1_xboole_0 = B_212
      | ~ r2_hidden(C_211,A_213)
      | ~ m1_subset_1(D_210,k1_zfmisc_1(k2_zfmisc_1(A_213,B_212)))
      | ~ v1_funct_2(D_210,A_213,B_212)
      | ~ v1_funct_1(D_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1581,plain,(
    ! [D_282,A_283,B_284,B_285] :
      ( r2_hidden(k1_funct_1(D_282,A_283),B_284)
      | k1_xboole_0 = B_284
      | ~ m1_subset_1(D_282,k1_zfmisc_1(k2_zfmisc_1(B_285,B_284)))
      | ~ v1_funct_2(D_282,B_285,B_284)
      | ~ v1_funct_1(D_282)
      | v1_xboole_0(B_285)
      | ~ m1_subset_1(A_283,B_285) ) ),
    inference(resolution,[status(thm)],[c_26,c_842])).

tff(c_1583,plain,(
    ! [A_283] :
      ( r2_hidden(k1_funct_1('#skF_5',A_283),k1_relat_1('#skF_6'))
      | k1_relat_1('#skF_6') = k1_xboole_0
      | ~ v1_funct_2('#skF_5','#skF_3',k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_283,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1116,c_1581])).

tff(c_1601,plain,(
    ! [A_283] :
      ( r2_hidden(k1_funct_1('#skF_5',A_283),k1_relat_1('#skF_6'))
      | k1_relat_1('#skF_6') = k1_xboole_0
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_283,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1051,c_1583])).

tff(c_1602,plain,(
    ! [A_283] :
      ( r2_hidden(k1_funct_1('#skF_5',A_283),k1_relat_1('#skF_6'))
      | k1_relat_1('#skF_6') = k1_xboole_0
      | ~ m1_subset_1(A_283,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_387,c_1601])).

tff(c_1704,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1602])).

tff(c_693,plain,(
    ! [C_191,A_192,B_193] :
      ( ~ v1_xboole_0(C_191)
      | ~ v1_funct_2(C_191,A_192,B_193)
      | ~ v1_funct_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193)))
      | v1_xboole_0(B_193)
      | v1_xboole_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_709,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_693])).

tff(c_721,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_709])).

tff(c_722,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_387,c_84,c_721])).

tff(c_24,plain,(
    ! [B_18,A_16] :
      ( v1_xboole_0(B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_16))
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1131,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1116,c_24])).

tff(c_1148,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_722,c_1131])).

tff(c_1709,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1704,c_1148])).

tff(c_1719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_18,c_1709])).

tff(c_1722,plain,(
    ! [A_290] :
      ( r2_hidden(k1_funct_1('#skF_5',A_290),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_290,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_1602])).

tff(c_48,plain,(
    ! [A_37,B_38,C_40] :
      ( k7_partfun1(A_37,B_38,C_40) = k1_funct_1(B_38,C_40)
      | ~ r2_hidden(C_40,k1_relat_1(B_38))
      | ~ v1_funct_1(B_38)
      | ~ v5_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1726,plain,(
    ! [A_37,A_290] :
      ( k7_partfun1(A_37,'#skF_6',k1_funct_1('#skF_5',A_290)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',A_290))
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_37)
      | ~ v1_relat_1('#skF_6')
      | ~ m1_subset_1(A_290,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1722,c_48])).

tff(c_1731,plain,(
    ! [A_291,A_292] :
      ( k7_partfun1(A_291,'#skF_6',k1_funct_1('#skF_5',A_292)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',A_292))
      | ~ v5_relat_1('#skF_6',A_291)
      | ~ m1_subset_1(A_292,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_76,c_1726])).

tff(c_66,plain,(
    k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5','#skF_7')) != k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1737,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ v5_relat_1('#skF_6','#skF_2')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1731,c_66])).

tff(c_1743,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_493,c_1737])).

tff(c_1771,plain,(
    ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1247,c_1743])).

tff(c_1775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1771])).

tff(c_1776,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1115])).

tff(c_1810,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1776,c_230])).

tff(c_1818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1810])).

tff(c_1819,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1050])).

tff(c_1851,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1819,c_230])).

tff(c_1859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1851])).

tff(c_1860,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_359])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1873,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1860,c_2])).

tff(c_1888,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1873,c_68])).

tff(c_1861,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_359])).

tff(c_1994,plain,(
    ! [A_305] :
      ( A_305 = '#skF_5'
      | ~ v1_xboole_0(A_305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1873,c_2])).

tff(c_2004,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1861,c_1994])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k2_zfmisc_1(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2240,plain,(
    ! [B_343,A_344] :
      ( B_343 = '#skF_5'
      | A_344 = '#skF_5'
      | k2_zfmisc_1(A_344,B_343) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1873,c_1873,c_1873,c_16])).

tff(c_2243,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2004,c_2240])).

tff(c_2252,plain,(
    '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1888,c_2243])).

tff(c_2280,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2252,c_1860])).

tff(c_2286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.93/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.07  
% 5.25/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.07  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.25/2.07  
% 5.25/2.07  %Foreground sorts:
% 5.25/2.07  
% 5.25/2.07  
% 5.25/2.07  %Background operators:
% 5.25/2.07  
% 5.25/2.07  
% 5.25/2.07  %Foreground operators:
% 5.25/2.07  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.25/2.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.25/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.25/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.25/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.25/2.07  tff('#skF_7', type, '#skF_7': $i).
% 5.25/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.25/2.07  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 5.25/2.07  tff('#skF_5', type, '#skF_5': $i).
% 5.25/2.07  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.25/2.07  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 5.25/2.07  tff('#skF_6', type, '#skF_6': $i).
% 5.25/2.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.25/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.25/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.25/2.07  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.25/2.07  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.25/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.25/2.07  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.25/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.25/2.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.25/2.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.25/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.25/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.25/2.07  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.25/2.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.25/2.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.25/2.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.25/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.25/2.07  
% 5.25/2.09  tff(f_216, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 5.25/2.09  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.25/2.09  tff(f_160, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 5.25/2.09  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.25/2.09  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.25/2.09  tff(f_49, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.25/2.09  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.25/2.09  tff(f_67, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.25/2.09  tff(f_70, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 5.25/2.09  tff(f_61, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 5.25/2.09  tff(f_57, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 5.25/2.09  tff(f_77, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.25/2.09  tff(f_191, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 5.25/2.09  tff(f_83, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.25/2.09  tff(f_172, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 5.25/2.09  tff(f_125, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 5.25/2.09  tff(f_136, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 5.25/2.09  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.25/2.09  tff(c_84, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.25/2.09  tff(c_72, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.25/2.09  tff(c_68, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.25/2.09  tff(c_82, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.25/2.09  tff(c_80, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.25/2.09  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.25/2.09  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.25/2.09  tff(c_538, plain, (![A_170, B_171, C_172]: (k1_relset_1(A_170, B_171, C_172)=k1_relat_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.25/2.09  tff(c_556, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_538])).
% 5.25/2.09  tff(c_70, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.25/2.09  tff(c_560, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_70])).
% 5.25/2.09  tff(c_76, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.25/2.09  tff(c_1187, plain, (![C_244, B_248, F_247, D_245, A_243, E_246]: (k1_funct_1(k8_funct_2(B_248, C_244, A_243, D_245, E_246), F_247)=k1_funct_1(E_246, k1_funct_1(D_245, F_247)) | k1_xboole_0=B_248 | ~r1_tarski(k2_relset_1(B_248, C_244, D_245), k1_relset_1(C_244, A_243, E_246)) | ~m1_subset_1(F_247, B_248) | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(C_244, A_243))) | ~v1_funct_1(E_246) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(B_248, C_244))) | ~v1_funct_2(D_245, B_248, C_244) | ~v1_funct_1(D_245) | v1_xboole_0(C_244))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.25/2.09  tff(c_1197, plain, (![B_248, D_245, F_247]: (k1_funct_1(k8_funct_2(B_248, '#skF_4', '#skF_2', D_245, '#skF_6'), F_247)=k1_funct_1('#skF_6', k1_funct_1(D_245, F_247)) | k1_xboole_0=B_248 | ~r1_tarski(k2_relset_1(B_248, '#skF_4', D_245), k1_relat_1('#skF_6')) | ~m1_subset_1(F_247, B_248) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(B_248, '#skF_4'))) | ~v1_funct_2(D_245, B_248, '#skF_4') | ~v1_funct_1(D_245) | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_556, c_1187])).
% 5.25/2.09  tff(c_1204, plain, (![B_248, D_245, F_247]: (k1_funct_1(k8_funct_2(B_248, '#skF_4', '#skF_2', D_245, '#skF_6'), F_247)=k1_funct_1('#skF_6', k1_funct_1(D_245, F_247)) | k1_xboole_0=B_248 | ~r1_tarski(k2_relset_1(B_248, '#skF_4', D_245), k1_relat_1('#skF_6')) | ~m1_subset_1(F_247, B_248) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(B_248, '#skF_4'))) | ~v1_funct_2(D_245, B_248, '#skF_4') | ~v1_funct_1(D_245) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1197])).
% 5.25/2.09  tff(c_1241, plain, (![B_252, D_253, F_254]: (k1_funct_1(k8_funct_2(B_252, '#skF_4', '#skF_2', D_253, '#skF_6'), F_254)=k1_funct_1('#skF_6', k1_funct_1(D_253, F_254)) | k1_xboole_0=B_252 | ~r1_tarski(k2_relset_1(B_252, '#skF_4', D_253), k1_relat_1('#skF_6')) | ~m1_subset_1(F_254, B_252) | ~m1_subset_1(D_253, k1_zfmisc_1(k2_zfmisc_1(B_252, '#skF_4'))) | ~v1_funct_2(D_253, B_252, '#skF_4') | ~v1_funct_1(D_253))), inference(negUnitSimplification, [status(thm)], [c_84, c_1204])).
% 5.25/2.09  tff(c_1243, plain, (![F_254]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_254)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_254)) | k1_xboole_0='#skF_3' | ~m1_subset_1(F_254, '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_560, c_1241])).
% 5.25/2.09  tff(c_1246, plain, (![F_254]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_254)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_254)) | k1_xboole_0='#skF_3' | ~m1_subset_1(F_254, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_1243])).
% 5.25/2.09  tff(c_1247, plain, (![F_254]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_254)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_254)) | ~m1_subset_1(F_254, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1246])).
% 5.25/2.09  tff(c_475, plain, (![C_154, B_155, A_156]: (v5_relat_1(C_154, B_155) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_156, B_155))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.25/2.09  tff(c_493, plain, (v5_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_475])).
% 5.25/2.09  tff(c_295, plain, (![C_121, A_122, B_123]: (v1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.25/2.09  tff(c_311, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_295])).
% 5.25/2.09  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.25/2.09  tff(c_216, plain, (![A_106, B_107]: (r2_hidden('#skF_1'(A_106, B_107), A_106) | r1_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.25/2.09  tff(c_18, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.25/2.09  tff(c_112, plain, (![A_82, B_83]: (~r2_hidden(A_82, k2_zfmisc_1(A_82, B_83)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.25/2.09  tff(c_118, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_112])).
% 5.25/2.09  tff(c_222, plain, (![B_108]: (r1_xboole_0(k1_xboole_0, B_108))), inference(resolution, [status(thm)], [c_216, c_118])).
% 5.25/2.09  tff(c_120, plain, (![A_85, B_86]: (v1_xboole_0(k2_zfmisc_1(A_85, B_86)) | ~v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.25/2.09  tff(c_132, plain, (![A_12]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_12))), inference(superposition, [status(thm), theory('equality')], [c_18, c_120])).
% 5.25/2.09  tff(c_135, plain, (![A_12]: (~v1_xboole_0(A_12))), inference(splitLeft, [status(thm)], [c_132])).
% 5.25/2.09  tff(c_12, plain, (![B_9, A_8]: (~r1_xboole_0(B_9, A_8) | ~r1_tarski(B_9, A_8) | v1_xboole_0(B_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.25/2.09  tff(c_153, plain, (![B_9, A_8]: (~r1_xboole_0(B_9, A_8) | ~r1_tarski(B_9, A_8))), inference(negUnitSimplification, [status(thm)], [c_135, c_12])).
% 5.25/2.09  tff(c_225, plain, (![B_108]: (~r1_tarski(k1_xboole_0, B_108))), inference(resolution, [status(thm)], [c_222, c_153])).
% 5.25/2.09  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_225])).
% 5.25/2.09  tff(c_230, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_132])).
% 5.25/2.09  tff(c_14, plain, (![A_10, B_11]: (v1_xboole_0(k2_zfmisc_1(A_10, B_11)) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.25/2.09  tff(c_347, plain, (![B_131, A_132]: (v1_xboole_0(B_131) | ~m1_subset_1(B_131, k1_zfmisc_1(A_132)) | ~v1_xboole_0(A_132))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.25/2.09  tff(c_359, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_347])).
% 5.25/2.09  tff(c_383, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_359])).
% 5.25/2.09  tff(c_387, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_14, c_383])).
% 5.25/2.09  tff(c_1045, plain, (![B_230, D_231, A_232, C_233]: (k1_xboole_0=B_230 | v1_funct_2(D_231, A_232, C_233) | ~r1_tarski(k2_relset_1(A_232, B_230, D_231), C_233) | ~m1_subset_1(D_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_230))) | ~v1_funct_2(D_231, A_232, B_230) | ~v1_funct_1(D_231))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.25/2.09  tff(c_1047, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', k1_relat_1('#skF_6')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_560, c_1045])).
% 5.25/2.09  tff(c_1050, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_1047])).
% 5.25/2.09  tff(c_1051, plain, (v1_funct_2('#skF_5', '#skF_3', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_1050])).
% 5.25/2.09  tff(c_1110, plain, (![B_239, D_240, A_241, C_242]: (k1_xboole_0=B_239 | m1_subset_1(D_240, k1_zfmisc_1(k2_zfmisc_1(A_241, C_242))) | ~r1_tarski(k2_relset_1(A_241, B_239, D_240), C_242) | ~m1_subset_1(D_240, k1_zfmisc_1(k2_zfmisc_1(A_241, B_239))) | ~v1_funct_2(D_240, A_241, B_239) | ~v1_funct_1(D_240))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.25/2.09  tff(c_1112, plain, (k1_xboole_0='#skF_4' | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_6')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_560, c_1110])).
% 5.25/2.09  tff(c_1115, plain, (k1_xboole_0='#skF_4' | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_1112])).
% 5.25/2.09  tff(c_1116, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_6'))))), inference(splitLeft, [status(thm)], [c_1115])).
% 5.25/2.09  tff(c_26, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.25/2.09  tff(c_842, plain, (![D_210, C_211, B_212, A_213]: (r2_hidden(k1_funct_1(D_210, C_211), B_212) | k1_xboole_0=B_212 | ~r2_hidden(C_211, A_213) | ~m1_subset_1(D_210, k1_zfmisc_1(k2_zfmisc_1(A_213, B_212))) | ~v1_funct_2(D_210, A_213, B_212) | ~v1_funct_1(D_210))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.25/2.09  tff(c_1581, plain, (![D_282, A_283, B_284, B_285]: (r2_hidden(k1_funct_1(D_282, A_283), B_284) | k1_xboole_0=B_284 | ~m1_subset_1(D_282, k1_zfmisc_1(k2_zfmisc_1(B_285, B_284))) | ~v1_funct_2(D_282, B_285, B_284) | ~v1_funct_1(D_282) | v1_xboole_0(B_285) | ~m1_subset_1(A_283, B_285))), inference(resolution, [status(thm)], [c_26, c_842])).
% 5.25/2.09  tff(c_1583, plain, (![A_283]: (r2_hidden(k1_funct_1('#skF_5', A_283), k1_relat_1('#skF_6')) | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_5', '#skF_3', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | ~m1_subset_1(A_283, '#skF_3'))), inference(resolution, [status(thm)], [c_1116, c_1581])).
% 5.25/2.09  tff(c_1601, plain, (![A_283]: (r2_hidden(k1_funct_1('#skF_5', A_283), k1_relat_1('#skF_6')) | k1_relat_1('#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_3') | ~m1_subset_1(A_283, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1051, c_1583])).
% 5.25/2.09  tff(c_1602, plain, (![A_283]: (r2_hidden(k1_funct_1('#skF_5', A_283), k1_relat_1('#skF_6')) | k1_relat_1('#skF_6')=k1_xboole_0 | ~m1_subset_1(A_283, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_387, c_1601])).
% 5.25/2.09  tff(c_1704, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1602])).
% 5.25/2.09  tff(c_693, plain, (![C_191, A_192, B_193]: (~v1_xboole_0(C_191) | ~v1_funct_2(C_191, A_192, B_193) | ~v1_funct_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))) | v1_xboole_0(B_193) | v1_xboole_0(A_192))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.25/2.09  tff(c_709, plain, (~v1_xboole_0('#skF_5') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_693])).
% 5.25/2.09  tff(c_721, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_709])).
% 5.25/2.09  tff(c_722, plain, (~v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_387, c_84, c_721])).
% 5.25/2.09  tff(c_24, plain, (![B_18, A_16]: (v1_xboole_0(B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_16)) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.25/2.09  tff(c_1131, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_1116, c_24])).
% 5.25/2.09  tff(c_1148, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_722, c_1131])).
% 5.25/2.09  tff(c_1709, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1704, c_1148])).
% 5.25/2.09  tff(c_1719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_230, c_18, c_1709])).
% 5.25/2.09  tff(c_1722, plain, (![A_290]: (r2_hidden(k1_funct_1('#skF_5', A_290), k1_relat_1('#skF_6')) | ~m1_subset_1(A_290, '#skF_3'))), inference(splitRight, [status(thm)], [c_1602])).
% 5.25/2.09  tff(c_48, plain, (![A_37, B_38, C_40]: (k7_partfun1(A_37, B_38, C_40)=k1_funct_1(B_38, C_40) | ~r2_hidden(C_40, k1_relat_1(B_38)) | ~v1_funct_1(B_38) | ~v5_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.25/2.09  tff(c_1726, plain, (![A_37, A_290]: (k7_partfun1(A_37, '#skF_6', k1_funct_1('#skF_5', A_290))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', A_290)) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_37) | ~v1_relat_1('#skF_6') | ~m1_subset_1(A_290, '#skF_3'))), inference(resolution, [status(thm)], [c_1722, c_48])).
% 5.25/2.09  tff(c_1731, plain, (![A_291, A_292]: (k7_partfun1(A_291, '#skF_6', k1_funct_1('#skF_5', A_292))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', A_292)) | ~v5_relat_1('#skF_6', A_291) | ~m1_subset_1(A_292, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_76, c_1726])).
% 5.25/2.09  tff(c_66, plain, (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', '#skF_7'))!=k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.25/2.09  tff(c_1737, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~v5_relat_1('#skF_6', '#skF_2') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1731, c_66])).
% 5.25/2.09  tff(c_1743, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_493, c_1737])).
% 5.25/2.09  tff(c_1771, plain, (~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1247, c_1743])).
% 5.25/2.09  tff(c_1775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_1771])).
% 5.25/2.09  tff(c_1776, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1115])).
% 5.25/2.09  tff(c_1810, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1776, c_230])).
% 5.25/2.09  tff(c_1818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1810])).
% 5.25/2.09  tff(c_1819, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1050])).
% 5.25/2.09  tff(c_1851, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1819, c_230])).
% 5.25/2.09  tff(c_1859, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1851])).
% 5.25/2.09  tff(c_1860, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_359])).
% 5.25/2.09  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.25/2.09  tff(c_1873, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1860, c_2])).
% 5.25/2.09  tff(c_1888, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1873, c_68])).
% 5.25/2.09  tff(c_1861, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_359])).
% 5.25/2.09  tff(c_1994, plain, (![A_305]: (A_305='#skF_5' | ~v1_xboole_0(A_305))), inference(demodulation, [status(thm), theory('equality')], [c_1873, c_2])).
% 5.25/2.09  tff(c_2004, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_1861, c_1994])).
% 5.25/2.09  tff(c_16, plain, (![B_13, A_12]: (k1_xboole_0=B_13 | k1_xboole_0=A_12 | k2_zfmisc_1(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.25/2.09  tff(c_2240, plain, (![B_343, A_344]: (B_343='#skF_5' | A_344='#skF_5' | k2_zfmisc_1(A_344, B_343)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1873, c_1873, c_1873, c_16])).
% 5.25/2.09  tff(c_2243, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2004, c_2240])).
% 5.25/2.09  tff(c_2252, plain, ('#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1888, c_2243])).
% 5.25/2.09  tff(c_2280, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2252, c_1860])).
% 5.25/2.09  tff(c_2286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_2280])).
% 5.25/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.09  
% 5.25/2.09  Inference rules
% 5.25/2.09  ----------------------
% 5.25/2.09  #Ref     : 0
% 5.25/2.09  #Sup     : 454
% 5.25/2.09  #Fact    : 0
% 5.25/2.09  #Define  : 0
% 5.25/2.09  #Split   : 13
% 5.25/2.09  #Chain   : 0
% 5.25/2.09  #Close   : 0
% 5.25/2.09  
% 5.25/2.09  Ordering : KBO
% 5.25/2.09  
% 5.25/2.09  Simplification rules
% 5.25/2.09  ----------------------
% 5.25/2.09  #Subsume      : 112
% 5.25/2.09  #Demod        : 569
% 5.25/2.09  #Tautology    : 229
% 5.25/2.09  #SimpNegUnit  : 28
% 5.25/2.09  #BackRed      : 195
% 5.25/2.10  
% 5.25/2.10  #Partial instantiations: 0
% 5.25/2.10  #Strategies tried      : 1
% 5.25/2.10  
% 5.25/2.10  Timing (in seconds)
% 5.25/2.10  ----------------------
% 5.25/2.10  Preprocessing        : 0.47
% 5.25/2.10  Parsing              : 0.23
% 5.25/2.10  CNF conversion       : 0.04
% 5.25/2.10  Main loop            : 0.78
% 5.25/2.10  Inferencing          : 0.25
% 5.25/2.10  Reduction            : 0.28
% 5.25/2.10  Demodulation         : 0.19
% 5.25/2.10  BG Simplification    : 0.04
% 5.25/2.10  Subsumption          : 0.15
% 5.25/2.10  Abstraction          : 0.04
% 5.25/2.10  MUC search           : 0.00
% 5.25/2.10  Cooper               : 0.00
% 5.25/2.10  Total                : 1.30
% 5.25/2.10  Index Insertion      : 0.00
% 5.25/2.10  Index Deletion       : 0.00
% 5.25/2.10  Index Matching       : 0.00
% 5.25/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
