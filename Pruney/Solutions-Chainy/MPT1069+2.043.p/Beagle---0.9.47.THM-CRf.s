%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:51 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 196 expanded)
%              Number of leaves         :   39 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  180 ( 696 expanded)
%              Number of equality atoms :   39 ( 141 expanded)
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

tff(f_133,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_108,axiom,(
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

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_34,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_115,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_123,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_115])).

tff(c_32,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_128,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_32])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_38,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1078,plain,(
    ! [A_252,B_250,F_249,C_247,D_251,E_248] :
      ( k1_funct_1(k8_funct_2(B_250,C_247,A_252,D_251,E_248),F_249) = k1_funct_1(E_248,k1_funct_1(D_251,F_249))
      | k1_xboole_0 = B_250
      | ~ r1_tarski(k2_relset_1(B_250,C_247,D_251),k1_relset_1(C_247,A_252,E_248))
      | ~ m1_subset_1(F_249,B_250)
      | ~ m1_subset_1(E_248,k1_zfmisc_1(k2_zfmisc_1(C_247,A_252)))
      | ~ v1_funct_1(E_248)
      | ~ m1_subset_1(D_251,k1_zfmisc_1(k2_zfmisc_1(B_250,C_247)))
      | ~ v1_funct_2(D_251,B_250,C_247)
      | ~ v1_funct_1(D_251)
      | v1_xboole_0(C_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1080,plain,(
    ! [B_250,D_251,F_249] :
      ( k1_funct_1(k8_funct_2(B_250,'#skF_4','#skF_2',D_251,'#skF_6'),F_249) = k1_funct_1('#skF_6',k1_funct_1(D_251,F_249))
      | k1_xboole_0 = B_250
      | ~ r1_tarski(k2_relset_1(B_250,'#skF_4',D_251),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_249,B_250)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_251,k1_zfmisc_1(k2_zfmisc_1(B_250,'#skF_4')))
      | ~ v1_funct_2(D_251,B_250,'#skF_4')
      | ~ v1_funct_1(D_251)
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_1078])).

tff(c_1082,plain,(
    ! [B_250,D_251,F_249] :
      ( k1_funct_1(k8_funct_2(B_250,'#skF_4','#skF_2',D_251,'#skF_6'),F_249) = k1_funct_1('#skF_6',k1_funct_1(D_251,F_249))
      | k1_xboole_0 = B_250
      | ~ r1_tarski(k2_relset_1(B_250,'#skF_4',D_251),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_249,B_250)
      | ~ m1_subset_1(D_251,k1_zfmisc_1(k2_zfmisc_1(B_250,'#skF_4')))
      | ~ v1_funct_2(D_251,B_250,'#skF_4')
      | ~ v1_funct_1(D_251)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1080])).

tff(c_1111,plain,(
    ! [B_255,D_256,F_257] :
      ( k1_funct_1(k8_funct_2(B_255,'#skF_4','#skF_2',D_256,'#skF_6'),F_257) = k1_funct_1('#skF_6',k1_funct_1(D_256,F_257))
      | k1_xboole_0 = B_255
      | ~ r1_tarski(k2_relset_1(B_255,'#skF_4',D_256),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_257,B_255)
      | ~ m1_subset_1(D_256,k1_zfmisc_1(k2_zfmisc_1(B_255,'#skF_4')))
      | ~ v1_funct_2(D_256,B_255,'#skF_4')
      | ~ v1_funct_1(D_256) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1082])).

tff(c_1113,plain,(
    ! [F_257] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_257) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_257))
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(F_257,'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_128,c_1111])).

tff(c_1116,plain,(
    ! [F_257] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_257) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_257))
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(F_257,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_1113])).

tff(c_1117,plain,(
    ! [F_257] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_257) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_257))
      | ~ m1_subset_1(F_257,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1116])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [C_68,B_69,A_70] :
      ( v5_relat_1(C_68,B_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_88,plain,(
    v5_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_80])).

tff(c_58,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_58])).

tff(c_639,plain,(
    ! [D_174,C_175,A_176,B_177] :
      ( r2_hidden(k1_funct_1(D_174,C_175),k2_relset_1(A_176,B_177,D_174))
      | k1_xboole_0 = B_177
      | ~ r2_hidden(C_175,A_176)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_funct_2(D_174,A_176,B_177)
      | ~ v1_funct_1(D_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1224,plain,(
    ! [A_282,C_281,D_280,B_283,B_284] :
      ( r2_hidden(k1_funct_1(D_280,C_281),B_284)
      | ~ r1_tarski(k2_relset_1(A_282,B_283,D_280),B_284)
      | k1_xboole_0 = B_283
      | ~ r2_hidden(C_281,A_282)
      | ~ m1_subset_1(D_280,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ v1_funct_2(D_280,A_282,B_283)
      | ~ v1_funct_1(D_280) ) ),
    inference(resolution,[status(thm)],[c_639,c_2])).

tff(c_1226,plain,(
    ! [C_281] :
      ( r2_hidden(k1_funct_1('#skF_5',C_281),k1_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_281,'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_128,c_1224])).

tff(c_1232,plain,(
    ! [C_281] :
      ( r2_hidden(k1_funct_1('#skF_5',C_281),k1_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_281,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_1226])).

tff(c_1234,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1232])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1246,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_8])).

tff(c_1249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1246])).

tff(c_1252,plain,(
    ! [C_285] :
      ( r2_hidden(k1_funct_1('#skF_5',C_285),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_285,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_1232])).

tff(c_22,plain,(
    ! [A_19,B_20,C_22] :
      ( k7_partfun1(A_19,B_20,C_22) = k1_funct_1(B_20,C_22)
      | ~ r2_hidden(C_22,k1_relat_1(B_20))
      | ~ v1_funct_1(B_20)
      | ~ v5_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1254,plain,(
    ! [A_19,C_285] :
      ( k7_partfun1(A_19,'#skF_6',k1_funct_1('#skF_5',C_285)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_285))
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_19)
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_285,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1252,c_22])).

tff(c_1291,plain,(
    ! [A_295,C_296] :
      ( k7_partfun1(A_295,'#skF_6',k1_funct_1('#skF_5',C_296)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_296))
      | ~ v5_relat_1('#skF_6',A_295)
      | ~ r2_hidden(C_296,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_38,c_1254])).

tff(c_28,plain,(
    k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5','#skF_7')) != k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1297,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ v5_relat_1('#skF_6','#skF_2')
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1291,c_28])).

tff(c_1303,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1297])).

tff(c_1305,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1303])).

tff(c_1308,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1305])).

tff(c_1311,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1308])).

tff(c_47,plain,(
    ! [B_55,A_56] :
      ( ~ v1_xboole_0(B_55)
      | B_55 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_8,c_47])).

tff(c_1314,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1311,c_50])).

tff(c_1320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1314])).

tff(c_1321,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1303])).

tff(c_1348,plain,(
    ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1117,c_1321])).

tff(c_1352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:32:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.63  
% 3.74/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.63  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.74/1.63  
% 3.74/1.63  %Foreground sorts:
% 3.74/1.63  
% 3.74/1.63  
% 3.74/1.63  %Background operators:
% 3.74/1.63  
% 3.74/1.63  
% 3.74/1.63  %Foreground operators:
% 3.74/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.74/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.74/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.74/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.74/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.74/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.63  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.74/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.74/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.74/1.63  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.74/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.74/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.74/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.74/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.74/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.74/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.74/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.74/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.74/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.74/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.74/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.74/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.74/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.74/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.74/1.63  
% 3.74/1.65  tff(f_133, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 3.74/1.65  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.74/1.65  tff(f_96, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 3.74/1.65  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.74/1.65  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.74/1.65  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.74/1.65  tff(f_108, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.74/1.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.74/1.65  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.74/1.65  tff(f_72, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 3.74/1.65  tff(f_41, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.74/1.65  tff(c_34, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.74/1.65  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.74/1.65  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.74/1.65  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.74/1.65  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.74/1.65  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.74/1.65  tff(c_115, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.74/1.65  tff(c_123, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_115])).
% 3.74/1.65  tff(c_32, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.74/1.65  tff(c_128, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_32])).
% 3.74/1.65  tff(c_46, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.74/1.65  tff(c_38, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.74/1.65  tff(c_1078, plain, (![A_252, B_250, F_249, C_247, D_251, E_248]: (k1_funct_1(k8_funct_2(B_250, C_247, A_252, D_251, E_248), F_249)=k1_funct_1(E_248, k1_funct_1(D_251, F_249)) | k1_xboole_0=B_250 | ~r1_tarski(k2_relset_1(B_250, C_247, D_251), k1_relset_1(C_247, A_252, E_248)) | ~m1_subset_1(F_249, B_250) | ~m1_subset_1(E_248, k1_zfmisc_1(k2_zfmisc_1(C_247, A_252))) | ~v1_funct_1(E_248) | ~m1_subset_1(D_251, k1_zfmisc_1(k2_zfmisc_1(B_250, C_247))) | ~v1_funct_2(D_251, B_250, C_247) | ~v1_funct_1(D_251) | v1_xboole_0(C_247))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.74/1.65  tff(c_1080, plain, (![B_250, D_251, F_249]: (k1_funct_1(k8_funct_2(B_250, '#skF_4', '#skF_2', D_251, '#skF_6'), F_249)=k1_funct_1('#skF_6', k1_funct_1(D_251, F_249)) | k1_xboole_0=B_250 | ~r1_tarski(k2_relset_1(B_250, '#skF_4', D_251), k1_relat_1('#skF_6')) | ~m1_subset_1(F_249, B_250) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_251, k1_zfmisc_1(k2_zfmisc_1(B_250, '#skF_4'))) | ~v1_funct_2(D_251, B_250, '#skF_4') | ~v1_funct_1(D_251) | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_1078])).
% 3.74/1.65  tff(c_1082, plain, (![B_250, D_251, F_249]: (k1_funct_1(k8_funct_2(B_250, '#skF_4', '#skF_2', D_251, '#skF_6'), F_249)=k1_funct_1('#skF_6', k1_funct_1(D_251, F_249)) | k1_xboole_0=B_250 | ~r1_tarski(k2_relset_1(B_250, '#skF_4', D_251), k1_relat_1('#skF_6')) | ~m1_subset_1(F_249, B_250) | ~m1_subset_1(D_251, k1_zfmisc_1(k2_zfmisc_1(B_250, '#skF_4'))) | ~v1_funct_2(D_251, B_250, '#skF_4') | ~v1_funct_1(D_251) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1080])).
% 3.74/1.65  tff(c_1111, plain, (![B_255, D_256, F_257]: (k1_funct_1(k8_funct_2(B_255, '#skF_4', '#skF_2', D_256, '#skF_6'), F_257)=k1_funct_1('#skF_6', k1_funct_1(D_256, F_257)) | k1_xboole_0=B_255 | ~r1_tarski(k2_relset_1(B_255, '#skF_4', D_256), k1_relat_1('#skF_6')) | ~m1_subset_1(F_257, B_255) | ~m1_subset_1(D_256, k1_zfmisc_1(k2_zfmisc_1(B_255, '#skF_4'))) | ~v1_funct_2(D_256, B_255, '#skF_4') | ~v1_funct_1(D_256))), inference(negUnitSimplification, [status(thm)], [c_46, c_1082])).
% 3.74/1.65  tff(c_1113, plain, (![F_257]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_257)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_257)) | k1_xboole_0='#skF_3' | ~m1_subset_1(F_257, '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_128, c_1111])).
% 3.74/1.65  tff(c_1116, plain, (![F_257]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_257)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_257)) | k1_xboole_0='#skF_3' | ~m1_subset_1(F_257, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_1113])).
% 3.74/1.65  tff(c_1117, plain, (![F_257]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_257)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_257)) | ~m1_subset_1(F_257, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_30, c_1116])).
% 3.74/1.65  tff(c_12, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.74/1.65  tff(c_80, plain, (![C_68, B_69, A_70]: (v5_relat_1(C_68, B_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.74/1.65  tff(c_88, plain, (v5_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_80])).
% 3.74/1.65  tff(c_58, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.74/1.65  tff(c_66, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_58])).
% 3.74/1.65  tff(c_639, plain, (![D_174, C_175, A_176, B_177]: (r2_hidden(k1_funct_1(D_174, C_175), k2_relset_1(A_176, B_177, D_174)) | k1_xboole_0=B_177 | ~r2_hidden(C_175, A_176) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_funct_2(D_174, A_176, B_177) | ~v1_funct_1(D_174))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.74/1.65  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.74/1.65  tff(c_1224, plain, (![A_282, C_281, D_280, B_283, B_284]: (r2_hidden(k1_funct_1(D_280, C_281), B_284) | ~r1_tarski(k2_relset_1(A_282, B_283, D_280), B_284) | k1_xboole_0=B_283 | ~r2_hidden(C_281, A_282) | ~m1_subset_1(D_280, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~v1_funct_2(D_280, A_282, B_283) | ~v1_funct_1(D_280))), inference(resolution, [status(thm)], [c_639, c_2])).
% 3.74/1.65  tff(c_1226, plain, (![C_281]: (r2_hidden(k1_funct_1('#skF_5', C_281), k1_relat_1('#skF_6')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_281, '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_128, c_1224])).
% 3.74/1.65  tff(c_1232, plain, (![C_281]: (r2_hidden(k1_funct_1('#skF_5', C_281), k1_relat_1('#skF_6')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_281, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_1226])).
% 3.74/1.65  tff(c_1234, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1232])).
% 3.74/1.65  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.65  tff(c_1246, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_8])).
% 3.74/1.65  tff(c_1249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1246])).
% 3.74/1.65  tff(c_1252, plain, (![C_285]: (r2_hidden(k1_funct_1('#skF_5', C_285), k1_relat_1('#skF_6')) | ~r2_hidden(C_285, '#skF_3'))), inference(splitRight, [status(thm)], [c_1232])).
% 3.74/1.65  tff(c_22, plain, (![A_19, B_20, C_22]: (k7_partfun1(A_19, B_20, C_22)=k1_funct_1(B_20, C_22) | ~r2_hidden(C_22, k1_relat_1(B_20)) | ~v1_funct_1(B_20) | ~v5_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.74/1.65  tff(c_1254, plain, (![A_19, C_285]: (k7_partfun1(A_19, '#skF_6', k1_funct_1('#skF_5', C_285))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_285)) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_19) | ~v1_relat_1('#skF_6') | ~r2_hidden(C_285, '#skF_3'))), inference(resolution, [status(thm)], [c_1252, c_22])).
% 3.74/1.65  tff(c_1291, plain, (![A_295, C_296]: (k7_partfun1(A_295, '#skF_6', k1_funct_1('#skF_5', C_296))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_296)) | ~v5_relat_1('#skF_6', A_295) | ~r2_hidden(C_296, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_38, c_1254])).
% 3.74/1.65  tff(c_28, plain, (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', '#skF_7'))!=k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.74/1.65  tff(c_1297, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~v5_relat_1('#skF_6', '#skF_2') | ~r2_hidden('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1291, c_28])).
% 3.74/1.65  tff(c_1303, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~r2_hidden('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1297])).
% 3.74/1.65  tff(c_1305, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_1303])).
% 3.74/1.65  tff(c_1308, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_1305])).
% 3.74/1.65  tff(c_1311, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1308])).
% 3.74/1.65  tff(c_47, plain, (![B_55, A_56]: (~v1_xboole_0(B_55) | B_55=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.74/1.65  tff(c_50, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_8, c_47])).
% 3.74/1.65  tff(c_1314, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1311, c_50])).
% 3.74/1.65  tff(c_1320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1314])).
% 3.74/1.65  tff(c_1321, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_1303])).
% 3.74/1.65  tff(c_1348, plain, (~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1117, c_1321])).
% 3.74/1.65  tff(c_1352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_1348])).
% 3.74/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.65  
% 3.74/1.65  Inference rules
% 3.74/1.65  ----------------------
% 3.74/1.65  #Ref     : 0
% 3.74/1.65  #Sup     : 271
% 3.74/1.65  #Fact    : 0
% 3.74/1.65  #Define  : 0
% 3.74/1.65  #Split   : 21
% 3.74/1.65  #Chain   : 0
% 3.74/1.65  #Close   : 0
% 3.74/1.65  
% 3.74/1.65  Ordering : KBO
% 3.74/1.65  
% 3.74/1.65  Simplification rules
% 3.74/1.65  ----------------------
% 3.74/1.65  #Subsume      : 57
% 3.74/1.65  #Demod        : 245
% 3.74/1.65  #Tautology    : 74
% 3.74/1.65  #SimpNegUnit  : 18
% 3.74/1.65  #BackRed      : 71
% 3.74/1.65  
% 3.74/1.65  #Partial instantiations: 0
% 3.74/1.65  #Strategies tried      : 1
% 3.74/1.65  
% 3.74/1.65  Timing (in seconds)
% 3.74/1.65  ----------------------
% 3.74/1.65  Preprocessing        : 0.33
% 3.74/1.65  Parsing              : 0.18
% 3.74/1.65  CNF conversion       : 0.03
% 3.74/1.65  Main loop            : 0.56
% 3.74/1.65  Inferencing          : 0.21
% 3.74/1.65  Reduction            : 0.17
% 3.74/1.65  Demodulation         : 0.12
% 3.74/1.65  BG Simplification    : 0.03
% 3.74/1.65  Subsumption          : 0.11
% 3.74/1.65  Abstraction          : 0.03
% 3.74/1.65  MUC search           : 0.00
% 3.74/1.65  Cooper               : 0.00
% 3.74/1.65  Total                : 0.93
% 3.74/1.65  Index Insertion      : 0.00
% 3.74/1.65  Index Deletion       : 0.00
% 3.74/1.65  Index Matching       : 0.00
% 3.74/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
