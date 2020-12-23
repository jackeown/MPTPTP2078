%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:51 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 193 expanded)
%              Number of leaves         :   39 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          :  176 ( 690 expanded)
%              Number of equality atoms :   38 ( 140 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_129,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_34,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_101,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_109,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_101])).

tff(c_32,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_114,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_32])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_38,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1204,plain,(
    ! [B_280,C_278,E_276,F_279,A_275,D_277] :
      ( k1_funct_1(k8_funct_2(B_280,C_278,A_275,D_277,E_276),F_279) = k1_funct_1(E_276,k1_funct_1(D_277,F_279))
      | k1_xboole_0 = B_280
      | ~ r1_tarski(k2_relset_1(B_280,C_278,D_277),k1_relset_1(C_278,A_275,E_276))
      | ~ m1_subset_1(F_279,B_280)
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1(C_278,A_275)))
      | ~ v1_funct_1(E_276)
      | ~ m1_subset_1(D_277,k1_zfmisc_1(k2_zfmisc_1(B_280,C_278)))
      | ~ v1_funct_2(D_277,B_280,C_278)
      | ~ v1_funct_1(D_277)
      | v1_xboole_0(C_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1208,plain,(
    ! [B_280,D_277,F_279] :
      ( k1_funct_1(k8_funct_2(B_280,'#skF_4','#skF_2',D_277,'#skF_6'),F_279) = k1_funct_1('#skF_6',k1_funct_1(D_277,F_279))
      | k1_xboole_0 = B_280
      | ~ r1_tarski(k2_relset_1(B_280,'#skF_4',D_277),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_279,B_280)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_277,k1_zfmisc_1(k2_zfmisc_1(B_280,'#skF_4')))
      | ~ v1_funct_2(D_277,B_280,'#skF_4')
      | ~ v1_funct_1(D_277)
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_1204])).

tff(c_1212,plain,(
    ! [B_280,D_277,F_279] :
      ( k1_funct_1(k8_funct_2(B_280,'#skF_4','#skF_2',D_277,'#skF_6'),F_279) = k1_funct_1('#skF_6',k1_funct_1(D_277,F_279))
      | k1_xboole_0 = B_280
      | ~ r1_tarski(k2_relset_1(B_280,'#skF_4',D_277),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_279,B_280)
      | ~ m1_subset_1(D_277,k1_zfmisc_1(k2_zfmisc_1(B_280,'#skF_4')))
      | ~ v1_funct_2(D_277,B_280,'#skF_4')
      | ~ v1_funct_1(D_277)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1208])).

tff(c_1215,plain,(
    ! [B_281,D_282,F_283] :
      ( k1_funct_1(k8_funct_2(B_281,'#skF_4','#skF_2',D_282,'#skF_6'),F_283) = k1_funct_1('#skF_6',k1_funct_1(D_282,F_283))
      | k1_xboole_0 = B_281
      | ~ r1_tarski(k2_relset_1(B_281,'#skF_4',D_282),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_283,B_281)
      | ~ m1_subset_1(D_282,k1_zfmisc_1(k2_zfmisc_1(B_281,'#skF_4')))
      | ~ v1_funct_2(D_282,B_281,'#skF_4')
      | ~ v1_funct_1(D_282) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1212])).

tff(c_1217,plain,(
    ! [F_283] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_283) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_283))
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(F_283,'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_114,c_1215])).

tff(c_1220,plain,(
    ! [F_283] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_283) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_283))
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(F_283,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_1217])).

tff(c_1221,plain,(
    ! [F_283] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_283) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_283))
      | ~ m1_subset_1(F_283,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1220])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [C_68,B_69,A_70] :
      ( v5_relat_1(C_68,B_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_91,plain,(
    v5_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_83])).

tff(c_54,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_54])).

tff(c_1086,plain,(
    ! [D_248,C_249,A_250,B_251] :
      ( r2_hidden(k1_funct_1(D_248,C_249),k2_relset_1(A_250,B_251,D_248))
      | k1_xboole_0 = B_251
      | ~ r2_hidden(C_249,A_250)
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251)))
      | ~ v1_funct_2(D_248,A_250,B_251)
      | ~ v1_funct_1(D_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1234,plain,(
    ! [D_289,A_288,B_286,C_285,B_287] :
      ( r2_hidden(k1_funct_1(D_289,C_285),B_287)
      | ~ r1_tarski(k2_relset_1(A_288,B_286,D_289),B_287)
      | k1_xboole_0 = B_286
      | ~ r2_hidden(C_285,A_288)
      | ~ m1_subset_1(D_289,k1_zfmisc_1(k2_zfmisc_1(A_288,B_286)))
      | ~ v1_funct_2(D_289,A_288,B_286)
      | ~ v1_funct_1(D_289) ) ),
    inference(resolution,[status(thm)],[c_1086,c_2])).

tff(c_1236,plain,(
    ! [C_285] :
      ( r2_hidden(k1_funct_1('#skF_5',C_285),k1_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_285,'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_114,c_1234])).

tff(c_1242,plain,(
    ! [C_285] :
      ( r2_hidden(k1_funct_1('#skF_5',C_285),k1_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_285,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_1236])).

tff(c_1244,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1242])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1256,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_8])).

tff(c_1259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1256])).

tff(c_1262,plain,(
    ! [C_290] :
      ( r2_hidden(k1_funct_1('#skF_5',C_290),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_290,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_1242])).

tff(c_22,plain,(
    ! [A_18,B_19,C_21] :
      ( k7_partfun1(A_18,B_19,C_21) = k1_funct_1(B_19,C_21)
      | ~ r2_hidden(C_21,k1_relat_1(B_19))
      | ~ v1_funct_1(B_19)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1264,plain,(
    ! [A_18,C_290] :
      ( k7_partfun1(A_18,'#skF_6',k1_funct_1('#skF_5',C_290)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_290))
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_18)
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_290,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1262,c_22])).

tff(c_1290,plain,(
    ! [A_296,C_297] :
      ( k7_partfun1(A_296,'#skF_6',k1_funct_1('#skF_5',C_297)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_297))
      | ~ v5_relat_1('#skF_6',A_296)
      | ~ r2_hidden(C_297,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_38,c_1264])).

tff(c_28,plain,(
    k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5','#skF_7')) != k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1296,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ v5_relat_1('#skF_6','#skF_2')
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1290,c_28])).

tff(c_1302,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1296])).

tff(c_1304,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1302])).

tff(c_1307,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1304])).

tff(c_1310,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1307])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1313,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1310,c_10])).

tff(c_1317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1313])).

tff(c_1318,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1302])).

tff(c_1344,plain,(
    ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1221,c_1318])).

tff(c_1348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.76  
% 3.96/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.76  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.96/1.76  
% 3.96/1.76  %Foreground sorts:
% 3.96/1.76  
% 3.96/1.76  
% 3.96/1.76  %Background operators:
% 3.96/1.76  
% 3.96/1.76  
% 3.96/1.76  %Foreground operators:
% 3.96/1.76  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.96/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.96/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.96/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.96/1.76  tff('#skF_7', type, '#skF_7': $i).
% 3.96/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/1.76  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.96/1.76  tff('#skF_5', type, '#skF_5': $i).
% 3.96/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.96/1.76  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.96/1.76  tff('#skF_6', type, '#skF_6': $i).
% 3.96/1.76  tff('#skF_2', type, '#skF_2': $i).
% 3.96/1.76  tff('#skF_3', type, '#skF_3': $i).
% 3.96/1.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.96/1.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.96/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.96/1.76  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.96/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.96/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.96/1.76  tff('#skF_4', type, '#skF_4': $i).
% 3.96/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.96/1.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.96/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.96/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.96/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.96/1.76  
% 3.96/1.78  tff(f_129, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 3.96/1.78  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.96/1.78  tff(f_92, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 3.96/1.78  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.96/1.78  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.96/1.78  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.96/1.78  tff(f_104, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.96/1.78  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.96/1.78  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.96/1.78  tff(f_68, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 3.96/1.78  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.96/1.78  tff(c_34, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.96/1.78  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.96/1.78  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.96/1.78  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.96/1.78  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.96/1.78  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.96/1.78  tff(c_101, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.96/1.78  tff(c_109, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_101])).
% 3.96/1.78  tff(c_32, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.96/1.78  tff(c_114, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_32])).
% 3.96/1.78  tff(c_46, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.96/1.78  tff(c_38, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.96/1.78  tff(c_1204, plain, (![B_280, C_278, E_276, F_279, A_275, D_277]: (k1_funct_1(k8_funct_2(B_280, C_278, A_275, D_277, E_276), F_279)=k1_funct_1(E_276, k1_funct_1(D_277, F_279)) | k1_xboole_0=B_280 | ~r1_tarski(k2_relset_1(B_280, C_278, D_277), k1_relset_1(C_278, A_275, E_276)) | ~m1_subset_1(F_279, B_280) | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1(C_278, A_275))) | ~v1_funct_1(E_276) | ~m1_subset_1(D_277, k1_zfmisc_1(k2_zfmisc_1(B_280, C_278))) | ~v1_funct_2(D_277, B_280, C_278) | ~v1_funct_1(D_277) | v1_xboole_0(C_278))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.96/1.78  tff(c_1208, plain, (![B_280, D_277, F_279]: (k1_funct_1(k8_funct_2(B_280, '#skF_4', '#skF_2', D_277, '#skF_6'), F_279)=k1_funct_1('#skF_6', k1_funct_1(D_277, F_279)) | k1_xboole_0=B_280 | ~r1_tarski(k2_relset_1(B_280, '#skF_4', D_277), k1_relat_1('#skF_6')) | ~m1_subset_1(F_279, B_280) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_277, k1_zfmisc_1(k2_zfmisc_1(B_280, '#skF_4'))) | ~v1_funct_2(D_277, B_280, '#skF_4') | ~v1_funct_1(D_277) | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_1204])).
% 3.96/1.78  tff(c_1212, plain, (![B_280, D_277, F_279]: (k1_funct_1(k8_funct_2(B_280, '#skF_4', '#skF_2', D_277, '#skF_6'), F_279)=k1_funct_1('#skF_6', k1_funct_1(D_277, F_279)) | k1_xboole_0=B_280 | ~r1_tarski(k2_relset_1(B_280, '#skF_4', D_277), k1_relat_1('#skF_6')) | ~m1_subset_1(F_279, B_280) | ~m1_subset_1(D_277, k1_zfmisc_1(k2_zfmisc_1(B_280, '#skF_4'))) | ~v1_funct_2(D_277, B_280, '#skF_4') | ~v1_funct_1(D_277) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1208])).
% 3.96/1.78  tff(c_1215, plain, (![B_281, D_282, F_283]: (k1_funct_1(k8_funct_2(B_281, '#skF_4', '#skF_2', D_282, '#skF_6'), F_283)=k1_funct_1('#skF_6', k1_funct_1(D_282, F_283)) | k1_xboole_0=B_281 | ~r1_tarski(k2_relset_1(B_281, '#skF_4', D_282), k1_relat_1('#skF_6')) | ~m1_subset_1(F_283, B_281) | ~m1_subset_1(D_282, k1_zfmisc_1(k2_zfmisc_1(B_281, '#skF_4'))) | ~v1_funct_2(D_282, B_281, '#skF_4') | ~v1_funct_1(D_282))), inference(negUnitSimplification, [status(thm)], [c_46, c_1212])).
% 3.96/1.78  tff(c_1217, plain, (![F_283]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_283)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_283)) | k1_xboole_0='#skF_3' | ~m1_subset_1(F_283, '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_114, c_1215])).
% 3.96/1.78  tff(c_1220, plain, (![F_283]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_283)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_283)) | k1_xboole_0='#skF_3' | ~m1_subset_1(F_283, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_1217])).
% 3.96/1.78  tff(c_1221, plain, (![F_283]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_283)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_283)) | ~m1_subset_1(F_283, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_30, c_1220])).
% 3.96/1.78  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.96/1.78  tff(c_83, plain, (![C_68, B_69, A_70]: (v5_relat_1(C_68, B_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.96/1.78  tff(c_91, plain, (v5_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_83])).
% 3.96/1.78  tff(c_54, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.96/1.78  tff(c_62, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_54])).
% 3.96/1.78  tff(c_1086, plain, (![D_248, C_249, A_250, B_251]: (r2_hidden(k1_funct_1(D_248, C_249), k2_relset_1(A_250, B_251, D_248)) | k1_xboole_0=B_251 | ~r2_hidden(C_249, A_250) | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))) | ~v1_funct_2(D_248, A_250, B_251) | ~v1_funct_1(D_248))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.96/1.78  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.96/1.78  tff(c_1234, plain, (![D_289, A_288, B_286, C_285, B_287]: (r2_hidden(k1_funct_1(D_289, C_285), B_287) | ~r1_tarski(k2_relset_1(A_288, B_286, D_289), B_287) | k1_xboole_0=B_286 | ~r2_hidden(C_285, A_288) | ~m1_subset_1(D_289, k1_zfmisc_1(k2_zfmisc_1(A_288, B_286))) | ~v1_funct_2(D_289, A_288, B_286) | ~v1_funct_1(D_289))), inference(resolution, [status(thm)], [c_1086, c_2])).
% 3.96/1.78  tff(c_1236, plain, (![C_285]: (r2_hidden(k1_funct_1('#skF_5', C_285), k1_relat_1('#skF_6')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_285, '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_114, c_1234])).
% 3.96/1.78  tff(c_1242, plain, (![C_285]: (r2_hidden(k1_funct_1('#skF_5', C_285), k1_relat_1('#skF_6')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_285, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_1236])).
% 3.96/1.78  tff(c_1244, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1242])).
% 3.96/1.78  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.96/1.78  tff(c_1256, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1244, c_8])).
% 3.96/1.78  tff(c_1259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1256])).
% 3.96/1.78  tff(c_1262, plain, (![C_290]: (r2_hidden(k1_funct_1('#skF_5', C_290), k1_relat_1('#skF_6')) | ~r2_hidden(C_290, '#skF_3'))), inference(splitRight, [status(thm)], [c_1242])).
% 3.96/1.78  tff(c_22, plain, (![A_18, B_19, C_21]: (k7_partfun1(A_18, B_19, C_21)=k1_funct_1(B_19, C_21) | ~r2_hidden(C_21, k1_relat_1(B_19)) | ~v1_funct_1(B_19) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.96/1.78  tff(c_1264, plain, (![A_18, C_290]: (k7_partfun1(A_18, '#skF_6', k1_funct_1('#skF_5', C_290))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_290)) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_18) | ~v1_relat_1('#skF_6') | ~r2_hidden(C_290, '#skF_3'))), inference(resolution, [status(thm)], [c_1262, c_22])).
% 3.96/1.78  tff(c_1290, plain, (![A_296, C_297]: (k7_partfun1(A_296, '#skF_6', k1_funct_1('#skF_5', C_297))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_297)) | ~v5_relat_1('#skF_6', A_296) | ~r2_hidden(C_297, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_38, c_1264])).
% 3.96/1.78  tff(c_28, plain, (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', '#skF_7'))!=k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.96/1.78  tff(c_1296, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~v5_relat_1('#skF_6', '#skF_2') | ~r2_hidden('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1290, c_28])).
% 3.96/1.78  tff(c_1302, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~r2_hidden('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_1296])).
% 3.96/1.78  tff(c_1304, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_1302])).
% 3.96/1.78  tff(c_1307, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_1304])).
% 3.96/1.78  tff(c_1310, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1307])).
% 3.96/1.78  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.96/1.78  tff(c_1313, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1310, c_10])).
% 3.96/1.78  tff(c_1317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1313])).
% 3.96/1.78  tff(c_1318, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_1302])).
% 3.96/1.78  tff(c_1344, plain, (~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1221, c_1318])).
% 3.96/1.78  tff(c_1348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_1344])).
% 3.96/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.78  
% 3.96/1.78  Inference rules
% 3.96/1.78  ----------------------
% 3.96/1.78  #Ref     : 0
% 3.96/1.78  #Sup     : 268
% 3.96/1.78  #Fact    : 0
% 3.96/1.78  #Define  : 0
% 3.96/1.78  #Split   : 19
% 3.96/1.78  #Chain   : 0
% 3.96/1.78  #Close   : 0
% 3.96/1.78  
% 3.96/1.78  Ordering : KBO
% 3.96/1.78  
% 3.96/1.78  Simplification rules
% 3.96/1.78  ----------------------
% 3.96/1.78  #Subsume      : 55
% 3.96/1.78  #Demod        : 257
% 3.96/1.78  #Tautology    : 80
% 3.96/1.78  #SimpNegUnit  : 16
% 3.96/1.78  #BackRed      : 78
% 3.96/1.78  
% 3.96/1.78  #Partial instantiations: 0
% 3.96/1.78  #Strategies tried      : 1
% 3.96/1.78  
% 3.96/1.78  Timing (in seconds)
% 3.96/1.78  ----------------------
% 3.96/1.78  Preprocessing        : 0.36
% 3.96/1.78  Parsing              : 0.20
% 3.96/1.78  CNF conversion       : 0.03
% 3.96/1.78  Main loop            : 0.59
% 3.96/1.78  Inferencing          : 0.22
% 3.96/1.78  Reduction            : 0.18
% 3.96/1.78  Demodulation         : 0.12
% 3.96/1.78  BG Simplification    : 0.03
% 3.96/1.78  Subsumption          : 0.12
% 3.96/1.78  Abstraction          : 0.03
% 3.96/1.78  MUC search           : 0.00
% 3.96/1.78  Cooper               : 0.00
% 3.96/1.78  Total                : 0.99
% 3.96/1.78  Index Insertion      : 0.00
% 3.96/1.78  Index Deletion       : 0.00
% 3.96/1.78  Index Matching       : 0.00
% 3.96/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
