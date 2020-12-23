%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:45 EST 2020

% Result     : Theorem 5.13s
% Output     : CNFRefutation 5.13s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 477 expanded)
%              Number of leaves         :   45 ( 186 expanded)
%              Depth                    :   17
%              Number of atoms          :  318 (1857 expanded)
%              Number of equality atoms :   66 ( 365 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_193,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_137,axiom,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_168,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_149,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

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

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_102,axiom,(
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

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_70,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_72,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_286,plain,(
    ! [A_122,B_123,C_124] :
      ( k1_relset_1(A_122,B_123,C_124) = k1_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_299,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_286])).

tff(c_68,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_303,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_68])).

tff(c_74,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_1364,plain,(
    ! [B_270,A_269,C_273,F_271,D_272,E_268] :
      ( k1_funct_1(k8_funct_2(B_270,C_273,A_269,D_272,E_268),F_271) = k1_funct_1(E_268,k1_funct_1(D_272,F_271))
      | k1_xboole_0 = B_270
      | ~ r1_tarski(k2_relset_1(B_270,C_273,D_272),k1_relset_1(C_273,A_269,E_268))
      | ~ m1_subset_1(F_271,B_270)
      | ~ m1_subset_1(E_268,k1_zfmisc_1(k2_zfmisc_1(C_273,A_269)))
      | ~ v1_funct_1(E_268)
      | ~ m1_subset_1(D_272,k1_zfmisc_1(k2_zfmisc_1(B_270,C_273)))
      | ~ v1_funct_2(D_272,B_270,C_273)
      | ~ v1_funct_1(D_272)
      | v1_xboole_0(C_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1370,plain,(
    ! [B_270,D_272,F_271] :
      ( k1_funct_1(k8_funct_2(B_270,'#skF_5','#skF_3',D_272,'#skF_7'),F_271) = k1_funct_1('#skF_7',k1_funct_1(D_272,F_271))
      | k1_xboole_0 = B_270
      | ~ r1_tarski(k2_relset_1(B_270,'#skF_5',D_272),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_271,B_270)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_272,k1_zfmisc_1(k2_zfmisc_1(B_270,'#skF_5')))
      | ~ v1_funct_2(D_272,B_270,'#skF_5')
      | ~ v1_funct_1(D_272)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_1364])).

tff(c_1379,plain,(
    ! [B_270,D_272,F_271] :
      ( k1_funct_1(k8_funct_2(B_270,'#skF_5','#skF_3',D_272,'#skF_7'),F_271) = k1_funct_1('#skF_7',k1_funct_1(D_272,F_271))
      | k1_xboole_0 = B_270
      | ~ r1_tarski(k2_relset_1(B_270,'#skF_5',D_272),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_271,B_270)
      | ~ m1_subset_1(D_272,k1_zfmisc_1(k2_zfmisc_1(B_270,'#skF_5')))
      | ~ v1_funct_2(D_272,B_270,'#skF_5')
      | ~ v1_funct_1(D_272)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1370])).

tff(c_1465,plain,(
    ! [B_283,D_284,F_285] :
      ( k1_funct_1(k8_funct_2(B_283,'#skF_5','#skF_3',D_284,'#skF_7'),F_285) = k1_funct_1('#skF_7',k1_funct_1(D_284,F_285))
      | k1_xboole_0 = B_283
      | ~ r1_tarski(k2_relset_1(B_283,'#skF_5',D_284),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_285,B_283)
      | ~ m1_subset_1(D_284,k1_zfmisc_1(k2_zfmisc_1(B_283,'#skF_5')))
      | ~ v1_funct_2(D_284,B_283,'#skF_5')
      | ~ v1_funct_1(D_284) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1379])).

tff(c_1467,plain,(
    ! [F_285] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_285) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_285))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_285,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_303,c_1465])).

tff(c_1473,plain,(
    ! [F_285] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_285) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_285))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_285,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_1467])).

tff(c_1474,plain,(
    ! [F_285] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_285) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_285))
      | ~ m1_subset_1(F_285,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1473])).

tff(c_243,plain,(
    ! [C_111,B_112,A_113] :
      ( v5_relat_1(C_111,B_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_256,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_243])).

tff(c_202,plain,(
    ! [C_99,A_100,B_101] :
      ( v1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_213,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_202])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1271,plain,(
    ! [B_257,D_258,A_259,C_260] :
      ( k1_xboole_0 = B_257
      | m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(A_259,C_260)))
      | ~ r1_tarski(k2_relset_1(A_259,B_257,D_258),C_260)
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(A_259,B_257)))
      | ~ v1_funct_2(D_258,A_259,B_257)
      | ~ v1_funct_1(D_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1401,plain,(
    ! [B_277,D_278,A_279] :
      ( k1_xboole_0 = B_277
      | m1_subset_1(D_278,k1_zfmisc_1(k2_zfmisc_1(A_279,k2_relset_1(A_279,B_277,D_278))))
      | ~ m1_subset_1(D_278,k1_zfmisc_1(k2_zfmisc_1(A_279,B_277)))
      | ~ v1_funct_2(D_278,A_279,B_277)
      | ~ v1_funct_1(D_278) ) ),
    inference(resolution,[status(thm)],[c_18,c_1271])).

tff(c_34,plain,(
    ! [C_25,B_24,A_23] :
      ( v5_relat_1(C_25,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1442,plain,(
    ! [D_280,A_281,B_282] :
      ( v5_relat_1(D_280,k2_relset_1(A_281,B_282,D_280))
      | k1_xboole_0 = B_282
      | ~ m1_subset_1(D_280,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282)))
      | ~ v1_funct_2(D_280,A_281,B_282)
      | ~ v1_funct_1(D_280) ) ),
    inference(resolution,[status(thm)],[c_1401,c_34])).

tff(c_1452,plain,
    ( v5_relat_1('#skF_6',k2_relset_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_5'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_1442])).

tff(c_1464,plain,
    ( v5_relat_1('#skF_6',k2_relset_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1452])).

tff(c_1476,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1464])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1508,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1476,c_12])).

tff(c_1511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1508])).

tff(c_1513,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1464])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | v1_xboole_0(B_18)
      | ~ m1_subset_1(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1079,plain,(
    ! [D_229,C_230,B_231,A_232] :
      ( r2_hidden(k1_funct_1(D_229,C_230),B_231)
      | k1_xboole_0 = B_231
      | ~ r2_hidden(C_230,A_232)
      | ~ m1_subset_1(D_229,k1_zfmisc_1(k2_zfmisc_1(A_232,B_231)))
      | ~ v1_funct_2(D_229,A_232,B_231)
      | ~ v1_funct_1(D_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1717,plain,(
    ! [D_313,A_314,B_315,B_316] :
      ( r2_hidden(k1_funct_1(D_313,A_314),B_315)
      | k1_xboole_0 = B_315
      | ~ m1_subset_1(D_313,k1_zfmisc_1(k2_zfmisc_1(B_316,B_315)))
      | ~ v1_funct_2(D_313,B_316,B_315)
      | ~ v1_funct_1(D_313)
      | v1_xboole_0(B_316)
      | ~ m1_subset_1(A_314,B_316) ) ),
    inference(resolution,[status(thm)],[c_28,c_1079])).

tff(c_1727,plain,(
    ! [A_314] :
      ( r2_hidden(k1_funct_1('#skF_6',A_314),'#skF_5')
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_314,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_1717])).

tff(c_1742,plain,(
    ! [A_314] :
      ( r2_hidden(k1_funct_1('#skF_6',A_314),'#skF_5')
      | k1_xboole_0 = '#skF_5'
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_314,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1727])).

tff(c_1743,plain,(
    ! [A_314] :
      ( r2_hidden(k1_funct_1('#skF_6',A_314),'#skF_5')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_314,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1513,c_1742])).

tff(c_1745,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1743])).

tff(c_120,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_2'(A_80,B_81),A_80)
      | r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [A_80,B_81] :
      ( ~ v1_xboole_0(A_80)
      | r1_tarski(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_120,c_2])).

tff(c_164,plain,(
    ! [B_92,A_93] :
      ( B_92 = A_93
      | ~ r1_tarski(B_92,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_178,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(B_94,A_95)
      | ~ v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_124,c_164])).

tff(c_192,plain,(
    ! [B_96,A_97] :
      ( B_96 = A_97
      | ~ v1_xboole_0(B_96)
      | ~ v1_xboole_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_124,c_178])).

tff(c_195,plain,(
    ! [A_97] :
      ( k1_xboole_0 = A_97
      | ~ v1_xboole_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_12,c_192])).

tff(c_1748,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1745,c_195])).

tff(c_1757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1748])).

tff(c_1759,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1743])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1182,plain,(
    ! [B_239,D_240,A_241,C_242] :
      ( k1_xboole_0 = B_239
      | v1_funct_2(D_240,A_241,C_242)
      | ~ r1_tarski(k2_relset_1(A_241,B_239,D_240),C_242)
      | ~ m1_subset_1(D_240,k1_zfmisc_1(k2_zfmisc_1(A_241,B_239)))
      | ~ v1_funct_2(D_240,A_241,B_239)
      | ~ v1_funct_1(D_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1184,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_303,c_1182])).

tff(c_1193,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_1184])).

tff(c_1196,plain,(
    v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1193])).

tff(c_1273,plain,
    ( k1_xboole_0 = '#skF_5'
    | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_303,c_1271])).

tff(c_1282,plain,
    ( k1_xboole_0 = '#skF_5'
    | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_1273])).

tff(c_1285,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7')))) ),
    inference(splitLeft,[status(thm)],[c_1282])).

tff(c_1446,plain,
    ( v5_relat_1('#skF_6',k2_relset_1('#skF_4',k1_relat_1('#skF_7'),'#skF_6'))
    | k1_relat_1('#skF_7') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1285,c_1442])).

tff(c_1458,plain,
    ( v5_relat_1('#skF_6',k2_relset_1('#skF_4',k1_relat_1('#skF_7'),'#skF_6'))
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1196,c_1446])).

tff(c_1519,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1458])).

tff(c_935,plain,(
    ! [C_196,A_197,B_198] :
      ( ~ v1_xboole_0(C_196)
      | ~ v1_funct_2(C_196,A_197,B_198)
      | ~ v1_funct_1(C_196)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | v1_xboole_0(B_198)
      | v1_xboole_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_944,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_935])).

tff(c_955,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_944])).

tff(c_956,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_955])).

tff(c_958,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_956])).

tff(c_26,plain,(
    ! [B_16,A_14] :
      ( v1_xboole_0(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_14))
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1305,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_1285,c_26])).

tff(c_1322,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_958,c_1305])).

tff(c_1551,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1519,c_1322])).

tff(c_1575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_22,c_1551])).

tff(c_1577,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1458])).

tff(c_1721,plain,(
    ! [A_314] :
      ( r2_hidden(k1_funct_1('#skF_6',A_314),k1_relat_1('#skF_7'))
      | k1_relat_1('#skF_7') = k1_xboole_0
      | ~ v1_funct_2('#skF_6','#skF_4',k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_314,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1285,c_1717])).

tff(c_1733,plain,(
    ! [A_314] :
      ( r2_hidden(k1_funct_1('#skF_6',A_314),k1_relat_1('#skF_7'))
      | k1_relat_1('#skF_7') = k1_xboole_0
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_314,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1196,c_1721])).

tff(c_1734,plain,(
    ! [A_314] :
      ( r2_hidden(k1_funct_1('#skF_6',A_314),k1_relat_1('#skF_7'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_314,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1577,c_1733])).

tff(c_1833,plain,(
    ! [A_324] :
      ( r2_hidden(k1_funct_1('#skF_6',A_324),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(A_324,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1759,c_1734])).

tff(c_46,plain,(
    ! [A_33,B_34,C_36] :
      ( k7_partfun1(A_33,B_34,C_36) = k1_funct_1(B_34,C_36)
      | ~ r2_hidden(C_36,k1_relat_1(B_34))
      | ~ v1_funct_1(B_34)
      | ~ v5_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1837,plain,(
    ! [A_33,A_324] :
      ( k7_partfun1(A_33,'#skF_7',k1_funct_1('#skF_6',A_324)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_324))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_33)
      | ~ v1_relat_1('#skF_7')
      | ~ m1_subset_1(A_324,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1833,c_46])).

tff(c_1915,plain,(
    ! [A_337,A_338] :
      ( k7_partfun1(A_337,'#skF_7',k1_funct_1('#skF_6',A_338)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_338))
      | ~ v5_relat_1('#skF_7',A_337)
      | ~ m1_subset_1(A_338,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_74,c_1837])).

tff(c_64,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_1921,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1915,c_64])).

tff(c_1927,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_256,c_1921])).

tff(c_1931,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1474,c_1927])).

tff(c_1935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1931])).

tff(c_1936,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1282])).

tff(c_1963,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1936,c_12])).

tff(c_1966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1963])).

tff(c_1967,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1193])).

tff(c_1988,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1967,c_12])).

tff(c_1991,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1988])).

tff(c_1992,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_956])).

tff(c_1996,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1992,c_195])).

tff(c_2005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1996])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.13/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/1.96  
% 5.13/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/1.96  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 5.13/1.96  
% 5.13/1.96  %Foreground sorts:
% 5.13/1.96  
% 5.13/1.96  
% 5.13/1.96  %Background operators:
% 5.13/1.96  
% 5.13/1.96  
% 5.13/1.96  %Foreground operators:
% 5.13/1.96  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.13/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.13/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.13/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.13/1.96  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.13/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.13/1.96  tff('#skF_7', type, '#skF_7': $i).
% 5.13/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.13/1.96  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 5.13/1.96  tff('#skF_5', type, '#skF_5': $i).
% 5.13/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.13/1.96  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 5.13/1.96  tff('#skF_6', type, '#skF_6': $i).
% 5.13/1.96  tff('#skF_3', type, '#skF_3': $i).
% 5.13/1.96  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.13/1.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.13/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.13/1.96  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.13/1.96  tff('#skF_8', type, '#skF_8': $i).
% 5.13/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.13/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.13/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.13/1.96  tff('#skF_4', type, '#skF_4': $i).
% 5.13/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.13/1.96  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.13/1.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.13/1.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.13/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.13/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.13/1.96  
% 5.13/1.98  tff(f_193, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 5.13/1.98  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.13/1.98  tff(f_137, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 5.13/1.98  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.13/1.98  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.13/1.98  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.13/1.98  tff(f_168, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 5.13/1.98  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.13/1.98  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.13/1.98  tff(f_149, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 5.13/1.98  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.13/1.98  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.13/1.98  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.13/1.98  tff(f_102, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 5.13/1.98  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.13/1.98  tff(f_113, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 5.13/1.98  tff(c_66, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.13/1.98  tff(c_82, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.13/1.98  tff(c_70, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.13/1.98  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.13/1.98  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.13/1.98  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.13/1.98  tff(c_72, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.13/1.98  tff(c_286, plain, (![A_122, B_123, C_124]: (k1_relset_1(A_122, B_123, C_124)=k1_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.13/1.98  tff(c_299, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_72, c_286])).
% 5.13/1.98  tff(c_68, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.13/1.98  tff(c_303, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_68])).
% 5.13/1.98  tff(c_74, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.13/1.98  tff(c_1364, plain, (![B_270, A_269, C_273, F_271, D_272, E_268]: (k1_funct_1(k8_funct_2(B_270, C_273, A_269, D_272, E_268), F_271)=k1_funct_1(E_268, k1_funct_1(D_272, F_271)) | k1_xboole_0=B_270 | ~r1_tarski(k2_relset_1(B_270, C_273, D_272), k1_relset_1(C_273, A_269, E_268)) | ~m1_subset_1(F_271, B_270) | ~m1_subset_1(E_268, k1_zfmisc_1(k2_zfmisc_1(C_273, A_269))) | ~v1_funct_1(E_268) | ~m1_subset_1(D_272, k1_zfmisc_1(k2_zfmisc_1(B_270, C_273))) | ~v1_funct_2(D_272, B_270, C_273) | ~v1_funct_1(D_272) | v1_xboole_0(C_273))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.13/1.98  tff(c_1370, plain, (![B_270, D_272, F_271]: (k1_funct_1(k8_funct_2(B_270, '#skF_5', '#skF_3', D_272, '#skF_7'), F_271)=k1_funct_1('#skF_7', k1_funct_1(D_272, F_271)) | k1_xboole_0=B_270 | ~r1_tarski(k2_relset_1(B_270, '#skF_5', D_272), k1_relat_1('#skF_7')) | ~m1_subset_1(F_271, B_270) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_272, k1_zfmisc_1(k2_zfmisc_1(B_270, '#skF_5'))) | ~v1_funct_2(D_272, B_270, '#skF_5') | ~v1_funct_1(D_272) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_299, c_1364])).
% 5.13/1.98  tff(c_1379, plain, (![B_270, D_272, F_271]: (k1_funct_1(k8_funct_2(B_270, '#skF_5', '#skF_3', D_272, '#skF_7'), F_271)=k1_funct_1('#skF_7', k1_funct_1(D_272, F_271)) | k1_xboole_0=B_270 | ~r1_tarski(k2_relset_1(B_270, '#skF_5', D_272), k1_relat_1('#skF_7')) | ~m1_subset_1(F_271, B_270) | ~m1_subset_1(D_272, k1_zfmisc_1(k2_zfmisc_1(B_270, '#skF_5'))) | ~v1_funct_2(D_272, B_270, '#skF_5') | ~v1_funct_1(D_272) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1370])).
% 5.13/1.98  tff(c_1465, plain, (![B_283, D_284, F_285]: (k1_funct_1(k8_funct_2(B_283, '#skF_5', '#skF_3', D_284, '#skF_7'), F_285)=k1_funct_1('#skF_7', k1_funct_1(D_284, F_285)) | k1_xboole_0=B_283 | ~r1_tarski(k2_relset_1(B_283, '#skF_5', D_284), k1_relat_1('#skF_7')) | ~m1_subset_1(F_285, B_283) | ~m1_subset_1(D_284, k1_zfmisc_1(k2_zfmisc_1(B_283, '#skF_5'))) | ~v1_funct_2(D_284, B_283, '#skF_5') | ~v1_funct_1(D_284))), inference(negUnitSimplification, [status(thm)], [c_82, c_1379])).
% 5.13/1.98  tff(c_1467, plain, (![F_285]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_285)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_285)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_285, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_303, c_1465])).
% 5.13/1.98  tff(c_1473, plain, (![F_285]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_285)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_285)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_285, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_1467])).
% 5.13/1.98  tff(c_1474, plain, (![F_285]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_285)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_285)) | ~m1_subset_1(F_285, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_1473])).
% 5.13/1.98  tff(c_243, plain, (![C_111, B_112, A_113]: (v5_relat_1(C_111, B_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.13/1.98  tff(c_256, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_243])).
% 5.13/1.98  tff(c_202, plain, (![C_99, A_100, B_101]: (v1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.13/1.98  tff(c_213, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_72, c_202])).
% 5.13/1.98  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.13/1.98  tff(c_1271, plain, (![B_257, D_258, A_259, C_260]: (k1_xboole_0=B_257 | m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(A_259, C_260))) | ~r1_tarski(k2_relset_1(A_259, B_257, D_258), C_260) | ~m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(A_259, B_257))) | ~v1_funct_2(D_258, A_259, B_257) | ~v1_funct_1(D_258))), inference(cnfTransformation, [status(thm)], [f_168])).
% 5.13/1.98  tff(c_1401, plain, (![B_277, D_278, A_279]: (k1_xboole_0=B_277 | m1_subset_1(D_278, k1_zfmisc_1(k2_zfmisc_1(A_279, k2_relset_1(A_279, B_277, D_278)))) | ~m1_subset_1(D_278, k1_zfmisc_1(k2_zfmisc_1(A_279, B_277))) | ~v1_funct_2(D_278, A_279, B_277) | ~v1_funct_1(D_278))), inference(resolution, [status(thm)], [c_18, c_1271])).
% 5.13/1.98  tff(c_34, plain, (![C_25, B_24, A_23]: (v5_relat_1(C_25, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.13/1.98  tff(c_1442, plain, (![D_280, A_281, B_282]: (v5_relat_1(D_280, k2_relset_1(A_281, B_282, D_280)) | k1_xboole_0=B_282 | ~m1_subset_1(D_280, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))) | ~v1_funct_2(D_280, A_281, B_282) | ~v1_funct_1(D_280))), inference(resolution, [status(thm)], [c_1401, c_34])).
% 5.13/1.98  tff(c_1452, plain, (v5_relat_1('#skF_6', k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_5' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_1442])).
% 5.13/1.98  tff(c_1464, plain, (v5_relat_1('#skF_6', k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1452])).
% 5.13/1.98  tff(c_1476, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1464])).
% 5.13/1.98  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.13/1.98  tff(c_1508, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1476, c_12])).
% 5.13/1.98  tff(c_1511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1508])).
% 5.13/1.98  tff(c_1513, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_1464])).
% 5.13/1.98  tff(c_28, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | v1_xboole_0(B_18) | ~m1_subset_1(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.13/1.98  tff(c_1079, plain, (![D_229, C_230, B_231, A_232]: (r2_hidden(k1_funct_1(D_229, C_230), B_231) | k1_xboole_0=B_231 | ~r2_hidden(C_230, A_232) | ~m1_subset_1(D_229, k1_zfmisc_1(k2_zfmisc_1(A_232, B_231))) | ~v1_funct_2(D_229, A_232, B_231) | ~v1_funct_1(D_229))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.13/1.98  tff(c_1717, plain, (![D_313, A_314, B_315, B_316]: (r2_hidden(k1_funct_1(D_313, A_314), B_315) | k1_xboole_0=B_315 | ~m1_subset_1(D_313, k1_zfmisc_1(k2_zfmisc_1(B_316, B_315))) | ~v1_funct_2(D_313, B_316, B_315) | ~v1_funct_1(D_313) | v1_xboole_0(B_316) | ~m1_subset_1(A_314, B_316))), inference(resolution, [status(thm)], [c_28, c_1079])).
% 5.13/1.98  tff(c_1727, plain, (![A_314]: (r2_hidden(k1_funct_1('#skF_6', A_314), '#skF_5') | k1_xboole_0='#skF_5' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_314, '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_1717])).
% 5.13/1.98  tff(c_1742, plain, (![A_314]: (r2_hidden(k1_funct_1('#skF_6', A_314), '#skF_5') | k1_xboole_0='#skF_5' | v1_xboole_0('#skF_4') | ~m1_subset_1(A_314, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1727])).
% 5.13/1.98  tff(c_1743, plain, (![A_314]: (r2_hidden(k1_funct_1('#skF_6', A_314), '#skF_5') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_314, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1513, c_1742])).
% 5.13/1.98  tff(c_1745, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1743])).
% 5.13/1.98  tff(c_120, plain, (![A_80, B_81]: (r2_hidden('#skF_2'(A_80, B_81), A_80) | r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.13/1.98  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.13/1.98  tff(c_124, plain, (![A_80, B_81]: (~v1_xboole_0(A_80) | r1_tarski(A_80, B_81))), inference(resolution, [status(thm)], [c_120, c_2])).
% 5.13/1.98  tff(c_164, plain, (![B_92, A_93]: (B_92=A_93 | ~r1_tarski(B_92, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.13/1.98  tff(c_178, plain, (![B_94, A_95]: (B_94=A_95 | ~r1_tarski(B_94, A_95) | ~v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_124, c_164])).
% 5.13/1.98  tff(c_192, plain, (![B_96, A_97]: (B_96=A_97 | ~v1_xboole_0(B_96) | ~v1_xboole_0(A_97))), inference(resolution, [status(thm)], [c_124, c_178])).
% 5.13/1.98  tff(c_195, plain, (![A_97]: (k1_xboole_0=A_97 | ~v1_xboole_0(A_97))), inference(resolution, [status(thm)], [c_12, c_192])).
% 5.13/1.98  tff(c_1748, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1745, c_195])).
% 5.13/1.98  tff(c_1757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1748])).
% 5.13/1.98  tff(c_1759, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1743])).
% 5.13/1.98  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.13/1.98  tff(c_1182, plain, (![B_239, D_240, A_241, C_242]: (k1_xboole_0=B_239 | v1_funct_2(D_240, A_241, C_242) | ~r1_tarski(k2_relset_1(A_241, B_239, D_240), C_242) | ~m1_subset_1(D_240, k1_zfmisc_1(k2_zfmisc_1(A_241, B_239))) | ~v1_funct_2(D_240, A_241, B_239) | ~v1_funct_1(D_240))), inference(cnfTransformation, [status(thm)], [f_168])).
% 5.13/1.98  tff(c_1184, plain, (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_303, c_1182])).
% 5.13/1.98  tff(c_1193, plain, (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_1184])).
% 5.13/1.98  tff(c_1196, plain, (v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1193])).
% 5.13/1.98  tff(c_1273, plain, (k1_xboole_0='#skF_5' | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_303, c_1271])).
% 5.13/1.98  tff(c_1282, plain, (k1_xboole_0='#skF_5' | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_1273])).
% 5.13/1.98  tff(c_1285, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7'))))), inference(splitLeft, [status(thm)], [c_1282])).
% 5.13/1.98  tff(c_1446, plain, (v5_relat_1('#skF_6', k2_relset_1('#skF_4', k1_relat_1('#skF_7'), '#skF_6')) | k1_relat_1('#skF_7')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_1285, c_1442])).
% 5.13/1.98  tff(c_1458, plain, (v5_relat_1('#skF_6', k2_relset_1('#skF_4', k1_relat_1('#skF_7'), '#skF_6')) | k1_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1196, c_1446])).
% 5.13/1.98  tff(c_1519, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1458])).
% 5.13/1.98  tff(c_935, plain, (![C_196, A_197, B_198]: (~v1_xboole_0(C_196) | ~v1_funct_2(C_196, A_197, B_198) | ~v1_funct_1(C_196) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | v1_xboole_0(B_198) | v1_xboole_0(A_197))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.13/1.98  tff(c_944, plain, (~v1_xboole_0('#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_76, c_935])).
% 5.13/1.98  tff(c_955, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_944])).
% 5.13/1.98  tff(c_956, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_955])).
% 5.13/1.98  tff(c_958, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_956])).
% 5.13/1.98  tff(c_26, plain, (![B_16, A_14]: (v1_xboole_0(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_14)) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.13/1.98  tff(c_1305, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_1285, c_26])).
% 5.13/1.98  tff(c_1322, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_958, c_1305])).
% 5.13/1.98  tff(c_1551, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1519, c_1322])).
% 5.13/1.98  tff(c_1575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_22, c_1551])).
% 5.13/1.98  tff(c_1577, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1458])).
% 5.13/1.98  tff(c_1721, plain, (![A_314]: (r2_hidden(k1_funct_1('#skF_6', A_314), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_4', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_314, '#skF_4'))), inference(resolution, [status(thm)], [c_1285, c_1717])).
% 5.13/1.98  tff(c_1733, plain, (![A_314]: (r2_hidden(k1_funct_1('#skF_6', A_314), k1_relat_1('#skF_7')) | k1_relat_1('#skF_7')=k1_xboole_0 | v1_xboole_0('#skF_4') | ~m1_subset_1(A_314, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1196, c_1721])).
% 5.13/1.98  tff(c_1734, plain, (![A_314]: (r2_hidden(k1_funct_1('#skF_6', A_314), k1_relat_1('#skF_7')) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_314, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1577, c_1733])).
% 5.13/1.98  tff(c_1833, plain, (![A_324]: (r2_hidden(k1_funct_1('#skF_6', A_324), k1_relat_1('#skF_7')) | ~m1_subset_1(A_324, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1759, c_1734])).
% 5.13/1.98  tff(c_46, plain, (![A_33, B_34, C_36]: (k7_partfun1(A_33, B_34, C_36)=k1_funct_1(B_34, C_36) | ~r2_hidden(C_36, k1_relat_1(B_34)) | ~v1_funct_1(B_34) | ~v5_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.13/1.98  tff(c_1837, plain, (![A_33, A_324]: (k7_partfun1(A_33, '#skF_7', k1_funct_1('#skF_6', A_324))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_324)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_33) | ~v1_relat_1('#skF_7') | ~m1_subset_1(A_324, '#skF_4'))), inference(resolution, [status(thm)], [c_1833, c_46])).
% 5.13/1.98  tff(c_1915, plain, (![A_337, A_338]: (k7_partfun1(A_337, '#skF_7', k1_funct_1('#skF_6', A_338))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_338)) | ~v5_relat_1('#skF_7', A_337) | ~m1_subset_1(A_338, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_74, c_1837])).
% 5.13/1.98  tff(c_64, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.13/1.98  tff(c_1921, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1915, c_64])).
% 5.13/1.98  tff(c_1927, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_256, c_1921])).
% 5.13/1.98  tff(c_1931, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1474, c_1927])).
% 5.13/1.98  tff(c_1935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1931])).
% 5.13/1.98  tff(c_1936, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1282])).
% 5.13/1.98  tff(c_1963, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1936, c_12])).
% 5.13/1.98  tff(c_1966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1963])).
% 5.13/1.98  tff(c_1967, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1193])).
% 5.13/1.98  tff(c_1988, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1967, c_12])).
% 5.13/1.98  tff(c_1991, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1988])).
% 5.13/1.98  tff(c_1992, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_956])).
% 5.13/1.98  tff(c_1996, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1992, c_195])).
% 5.13/1.98  tff(c_2005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1996])).
% 5.13/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/1.98  
% 5.13/1.98  Inference rules
% 5.13/1.98  ----------------------
% 5.13/1.98  #Ref     : 0
% 5.13/1.98  #Sup     : 404
% 5.13/1.98  #Fact    : 0
% 5.13/1.98  #Define  : 0
% 5.13/1.98  #Split   : 26
% 5.13/1.98  #Chain   : 0
% 5.13/1.98  #Close   : 0
% 5.13/1.98  
% 5.13/1.98  Ordering : KBO
% 5.13/1.98  
% 5.13/1.98  Simplification rules
% 5.13/1.98  ----------------------
% 5.13/1.98  #Subsume      : 107
% 5.13/1.98  #Demod        : 408
% 5.13/1.98  #Tautology    : 101
% 5.13/1.98  #SimpNegUnit  : 36
% 5.13/1.98  #BackRed      : 148
% 5.13/1.98  
% 5.13/1.98  #Partial instantiations: 0
% 5.13/1.98  #Strategies tried      : 1
% 5.13/1.98  
% 5.13/1.98  Timing (in seconds)
% 5.13/1.98  ----------------------
% 5.13/1.98  Preprocessing        : 0.38
% 5.13/1.98  Parsing              : 0.19
% 5.13/1.98  CNF conversion       : 0.03
% 5.13/1.98  Main loop            : 0.83
% 5.13/1.98  Inferencing          : 0.25
% 5.13/1.98  Reduction            : 0.25
% 5.13/1.98  Demodulation         : 0.17
% 5.13/1.98  BG Simplification    : 0.04
% 5.13/1.98  Subsumption          : 0.23
% 5.13/1.98  Abstraction          : 0.04
% 5.13/1.98  MUC search           : 0.00
% 5.13/1.98  Cooper               : 0.00
% 5.13/1.98  Total                : 1.25
% 5.13/1.98  Index Insertion      : 0.00
% 5.13/1.98  Index Deletion       : 0.00
% 5.13/1.98  Index Matching       : 0.00
% 5.13/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
