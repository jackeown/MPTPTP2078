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
% DateTime   : Thu Dec  3 10:18:13 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.96s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 277 expanded)
%              Number of leaves         :   40 ( 116 expanded)
%              Depth                    :   16
%              Number of atoms          :  249 (1095 expanded)
%              Number of equality atoms :   38 ( 126 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_176,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                   => ! [F] :
                        ( m1_subset_1(F,B)
                       => ( v1_partfun1(E,A)
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k7_partfun1(C,E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_137,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C,D] :
              ( ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
             => ! [E] :
                  ( ( v1_funct_1(E)
                    & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                 => ! [F] :
                      ( m1_subset_1(F,B)
                     => ( v1_partfun1(E,A)
                       => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k1_funct_1(E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_149,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_111,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( m1_subset_1(D,A)
                 => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(c_40,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_551,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( k3_funct_2(A_185,B_186,C_187,D_188) = k1_funct_1(C_187,D_188)
      | ~ m1_subset_1(D_188,A_185)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ v1_funct_2(C_187,A_185,B_186)
      | ~ v1_funct_1(C_187)
      | v1_xboole_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_573,plain,(
    ! [B_186,C_187] :
      ( k3_funct_2('#skF_2',B_186,C_187,'#skF_6') = k1_funct_1(C_187,'#skF_6')
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_186)))
      | ~ v1_funct_2(C_187,'#skF_2',B_186)
      | ~ v1_funct_1(C_187)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_551])).

tff(c_671,plain,(
    ! [B_195,C_196] :
      ( k3_funct_2('#skF_2',B_195,C_196,'#skF_6') = k1_funct_1(C_196,'#skF_6')
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_195)))
      | ~ v1_funct_2(C_196,'#skF_2',B_195)
      | ~ v1_funct_1(C_196) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_573])).

tff(c_682,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_671])).

tff(c_687,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_682])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_38,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_889,plain,(
    ! [A_230,C_231,B_228,F_227,E_232,D_229] :
      ( k3_funct_2(B_228,C_231,k8_funct_2(B_228,A_230,C_231,D_229,E_232),F_227) = k1_funct_1(E_232,k3_funct_2(B_228,A_230,D_229,F_227))
      | ~ v1_partfun1(E_232,A_230)
      | ~ m1_subset_1(F_227,B_228)
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(A_230,C_231)))
      | ~ v1_funct_1(E_232)
      | ~ m1_subset_1(D_229,k1_zfmisc_1(k2_zfmisc_1(B_228,A_230)))
      | ~ v1_funct_2(D_229,B_228,A_230)
      | ~ v1_funct_1(D_229)
      | v1_xboole_0(B_228)
      | v1_xboole_0(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_903,plain,(
    ! [B_228,D_229,F_227] :
      ( k3_funct_2(B_228,'#skF_3',k8_funct_2(B_228,'#skF_1','#skF_3',D_229,'#skF_5'),F_227) = k1_funct_1('#skF_5',k3_funct_2(B_228,'#skF_1',D_229,F_227))
      | ~ v1_partfun1('#skF_5','#skF_1')
      | ~ m1_subset_1(F_227,B_228)
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_229,k1_zfmisc_1(k2_zfmisc_1(B_228,'#skF_1')))
      | ~ v1_funct_2(D_229,B_228,'#skF_1')
      | ~ v1_funct_1(D_229)
      | v1_xboole_0(B_228)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_889])).

tff(c_917,plain,(
    ! [B_228,D_229,F_227] :
      ( k3_funct_2(B_228,'#skF_3',k8_funct_2(B_228,'#skF_1','#skF_3',D_229,'#skF_5'),F_227) = k1_funct_1('#skF_5',k3_funct_2(B_228,'#skF_1',D_229,F_227))
      | ~ m1_subset_1(F_227,B_228)
      | ~ m1_subset_1(D_229,k1_zfmisc_1(k2_zfmisc_1(B_228,'#skF_1')))
      | ~ v1_funct_2(D_229,B_228,'#skF_1')
      | ~ v1_funct_1(D_229)
      | v1_xboole_0(B_228)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_903])).

tff(c_1355,plain,(
    ! [B_290,D_291,F_292] :
      ( k3_funct_2(B_290,'#skF_3',k8_funct_2(B_290,'#skF_1','#skF_3',D_291,'#skF_5'),F_292) = k1_funct_1('#skF_5',k3_funct_2(B_290,'#skF_1',D_291,F_292))
      | ~ m1_subset_1(F_292,B_290)
      | ~ m1_subset_1(D_291,k1_zfmisc_1(k2_zfmisc_1(B_290,'#skF_1')))
      | ~ v1_funct_2(D_291,B_290,'#skF_1')
      | ~ v1_funct_1(D_291)
      | v1_xboole_0(B_290) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_917])).

tff(c_1372,plain,(
    ! [F_292] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_292) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_292))
      | ~ m1_subset_1(F_292,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_1355])).

tff(c_1383,plain,(
    ! [F_292] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_292) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_292))
      | ~ m1_subset_1(F_292,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1372])).

tff(c_1385,plain,(
    ! [F_293] :
      ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_293) = k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4',F_293))
      | ~ m1_subset_1(F_293,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1383])).

tff(c_201,plain,(
    ! [C_141,A_142,B_143] :
      ( ~ v1_partfun1(C_141,A_142)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ v1_xboole_0(B_143)
      | v1_xboole_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_211,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_201])).

tff(c_217,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_211])).

tff(c_218,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_217])).

tff(c_168,plain,(
    ! [A_135,B_136,C_137] :
      ( k2_relset_1(A_135,B_136,C_137) = k2_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_181,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_168])).

tff(c_232,plain,(
    ! [A_147,B_148,C_149] :
      ( m1_subset_1(k2_relset_1(A_147,B_148,C_149),k1_zfmisc_1(B_148))
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_258,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_232])).

tff(c_269,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_258])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_275,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_269,c_2])).

tff(c_69,plain,(
    ! [C_114,A_115,B_116] :
      ( v1_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_69])).

tff(c_119,plain,(
    ! [C_126,A_127,B_128] :
      ( v4_relat_1(C_126,A_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_132,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_119])).

tff(c_145,plain,(
    ! [B_133,A_134] :
      ( k1_relat_1(B_133) = A_134
      | ~ v1_partfun1(B_133,A_134)
      | ~ v4_relat_1(B_133,A_134)
      | ~ v1_relat_1(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_148,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_132,c_145])).

tff(c_154,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_38,c_148])).

tff(c_333,plain,(
    ! [B_156,A_157] :
      ( v1_funct_2(B_156,k1_relat_1(B_156),A_157)
      | ~ r1_tarski(k2_relat_1(B_156),A_157)
      | ~ v1_funct_1(B_156)
      | ~ v1_relat_1(B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_336,plain,(
    ! [A_157] :
      ( v1_funct_2('#skF_5','#skF_1',A_157)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_157)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_333])).

tff(c_339,plain,(
    ! [A_158] :
      ( v1_funct_2('#skF_5','#skF_1',A_158)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_44,c_336])).

tff(c_343,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_275,c_339])).

tff(c_469,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( m1_subset_1(k3_funct_2(A_170,B_171,C_172,D_173),B_171)
      | ~ m1_subset_1(D_173,A_170)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171)))
      | ~ v1_funct_2(C_172,A_170,B_171)
      | ~ v1_funct_1(C_172)
      | v1_xboole_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_481,plain,(
    ! [D_173] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_173),'#skF_1')
      | ~ m1_subset_1(D_173,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_469])).

tff(c_493,plain,(
    ! [D_173] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_173),'#skF_1')
      | ~ m1_subset_1(D_173,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_481])).

tff(c_494,plain,(
    ! [D_173] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_173),'#skF_1')
      | ~ m1_subset_1(D_173,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_493])).

tff(c_692,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_687,c_494])).

tff(c_696,plain,(
    m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_692])).

tff(c_24,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( k3_funct_2(A_25,B_26,C_27,D_28) = k1_funct_1(C_27,D_28)
      | ~ m1_subset_1(D_28,A_25)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ v1_funct_1(C_27)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_699,plain,(
    ! [B_26,C_27] :
      ( k3_funct_2('#skF_1',B_26,C_27,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_27,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_26)))
      | ~ v1_funct_2(C_27,'#skF_1',B_26)
      | ~ v1_funct_1(C_27)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_696,c_24])).

tff(c_961,plain,(
    ! [B_245,C_246] :
      ( k3_funct_2('#skF_1',B_245,C_246,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_246,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_245)))
      | ~ v1_funct_2(C_246,'#skF_1',B_245)
      | ~ v1_funct_1(C_246) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_699])).

tff(c_975,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_961])).

tff(c_983,plain,(
    k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_343,c_975])).

tff(c_751,plain,(
    ! [A_203,B_204,C_205,D_206] :
      ( k3_funct_2(A_203,B_204,C_205,D_206) = k7_partfun1(B_204,C_205,D_206)
      | ~ m1_subset_1(D_206,A_203)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204)))
      | ~ v1_funct_2(C_205,A_203,B_204)
      | ~ v1_funct_1(C_205)
      | v1_xboole_0(B_204)
      | v1_xboole_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_753,plain,(
    ! [B_204,C_205] :
      ( k3_funct_2('#skF_1',B_204,C_205,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_204,C_205,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_204)))
      | ~ v1_funct_2(C_205,'#skF_1',B_204)
      | ~ v1_funct_1(C_205)
      | v1_xboole_0(B_204)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_696,c_751])).

tff(c_1114,plain,(
    ! [B_265,C_266] :
      ( k3_funct_2('#skF_1',B_265,C_266,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_265,C_266,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_265)))
      | ~ v1_funct_2(C_266,'#skF_1',B_265)
      | ~ v1_funct_1(C_266)
      | v1_xboole_0(B_265) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_753])).

tff(c_1128,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1114])).

tff(c_1136,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_343,c_983,c_1128])).

tff(c_1137,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_1136])).

tff(c_36,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_688,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_36])).

tff(c_1138,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1137,c_688])).

tff(c_1391,plain,
    ( k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1385,c_1138])).

tff(c_1398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_687,c_1391])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:35:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.64/2.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.64/2.31  
% 5.64/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.64/2.32  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.64/2.32  
% 5.64/2.32  %Foreground sorts:
% 5.64/2.32  
% 5.64/2.32  
% 5.64/2.32  %Background operators:
% 5.64/2.32  
% 5.64/2.32  
% 5.64/2.32  %Foreground operators:
% 5.64/2.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.64/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.64/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.64/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.64/2.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.64/2.32  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 5.64/2.32  tff('#skF_5', type, '#skF_5': $i).
% 5.64/2.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.64/2.32  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 5.64/2.32  tff('#skF_6', type, '#skF_6': $i).
% 5.64/2.32  tff('#skF_2', type, '#skF_2': $i).
% 5.64/2.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.64/2.32  tff('#skF_3', type, '#skF_3': $i).
% 5.64/2.32  tff('#skF_1', type, '#skF_1': $i).
% 5.64/2.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.64/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.64/2.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.64/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.64/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.64/2.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.64/2.32  tff('#skF_4', type, '#skF_4': $i).
% 5.64/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.64/2.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.64/2.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.64/2.32  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 5.64/2.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.64/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.64/2.32  
% 5.64/2.35  tff(f_176, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_funct_2)).
% 5.64/2.35  tff(f_92, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 5.64/2.35  tff(f_137, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_funct_2)).
% 5.64/2.35  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_partfun1)).
% 5.64/2.35  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.64/2.35  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.64/2.35  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.64/2.35  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.64/2.35  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.64/2.35  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 5.64/2.35  tff(f_149, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 5.64/2.35  tff(f_79, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 5.64/2.35  tff(f_111, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 5.64/2.35  tff(c_40, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.64/2.35  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.64/2.35  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.64/2.35  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.64/2.35  tff(c_52, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.64/2.35  tff(c_551, plain, (![A_185, B_186, C_187, D_188]: (k3_funct_2(A_185, B_186, C_187, D_188)=k1_funct_1(C_187, D_188) | ~m1_subset_1(D_188, A_185) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~v1_funct_2(C_187, A_185, B_186) | ~v1_funct_1(C_187) | v1_xboole_0(A_185))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.64/2.35  tff(c_573, plain, (![B_186, C_187]: (k3_funct_2('#skF_2', B_186, C_187, '#skF_6')=k1_funct_1(C_187, '#skF_6') | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_186))) | ~v1_funct_2(C_187, '#skF_2', B_186) | ~v1_funct_1(C_187) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_551])).
% 5.64/2.35  tff(c_671, plain, (![B_195, C_196]: (k3_funct_2('#skF_2', B_195, C_196, '#skF_6')=k1_funct_1(C_196, '#skF_6') | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_195))) | ~v1_funct_2(C_196, '#skF_2', B_195) | ~v1_funct_1(C_196))), inference(negUnitSimplification, [status(thm)], [c_52, c_573])).
% 5.64/2.35  tff(c_682, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_671])).
% 5.64/2.35  tff(c_687, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_682])).
% 5.64/2.35  tff(c_54, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.64/2.35  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.64/2.35  tff(c_38, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.64/2.35  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.64/2.35  tff(c_889, plain, (![A_230, C_231, B_228, F_227, E_232, D_229]: (k3_funct_2(B_228, C_231, k8_funct_2(B_228, A_230, C_231, D_229, E_232), F_227)=k1_funct_1(E_232, k3_funct_2(B_228, A_230, D_229, F_227)) | ~v1_partfun1(E_232, A_230) | ~m1_subset_1(F_227, B_228) | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(A_230, C_231))) | ~v1_funct_1(E_232) | ~m1_subset_1(D_229, k1_zfmisc_1(k2_zfmisc_1(B_228, A_230))) | ~v1_funct_2(D_229, B_228, A_230) | ~v1_funct_1(D_229) | v1_xboole_0(B_228) | v1_xboole_0(A_230))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.64/2.35  tff(c_903, plain, (![B_228, D_229, F_227]: (k3_funct_2(B_228, '#skF_3', k8_funct_2(B_228, '#skF_1', '#skF_3', D_229, '#skF_5'), F_227)=k1_funct_1('#skF_5', k3_funct_2(B_228, '#skF_1', D_229, F_227)) | ~v1_partfun1('#skF_5', '#skF_1') | ~m1_subset_1(F_227, B_228) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_229, k1_zfmisc_1(k2_zfmisc_1(B_228, '#skF_1'))) | ~v1_funct_2(D_229, B_228, '#skF_1') | ~v1_funct_1(D_229) | v1_xboole_0(B_228) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_889])).
% 5.64/2.35  tff(c_917, plain, (![B_228, D_229, F_227]: (k3_funct_2(B_228, '#skF_3', k8_funct_2(B_228, '#skF_1', '#skF_3', D_229, '#skF_5'), F_227)=k1_funct_1('#skF_5', k3_funct_2(B_228, '#skF_1', D_229, F_227)) | ~m1_subset_1(F_227, B_228) | ~m1_subset_1(D_229, k1_zfmisc_1(k2_zfmisc_1(B_228, '#skF_1'))) | ~v1_funct_2(D_229, B_228, '#skF_1') | ~v1_funct_1(D_229) | v1_xboole_0(B_228) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_903])).
% 5.64/2.35  tff(c_1355, plain, (![B_290, D_291, F_292]: (k3_funct_2(B_290, '#skF_3', k8_funct_2(B_290, '#skF_1', '#skF_3', D_291, '#skF_5'), F_292)=k1_funct_1('#skF_5', k3_funct_2(B_290, '#skF_1', D_291, F_292)) | ~m1_subset_1(F_292, B_290) | ~m1_subset_1(D_291, k1_zfmisc_1(k2_zfmisc_1(B_290, '#skF_1'))) | ~v1_funct_2(D_291, B_290, '#skF_1') | ~v1_funct_1(D_291) | v1_xboole_0(B_290))), inference(negUnitSimplification, [status(thm)], [c_54, c_917])).
% 5.64/2.35  tff(c_1372, plain, (![F_292]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_292)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_292)) | ~m1_subset_1(F_292, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_1355])).
% 5.96/2.35  tff(c_1383, plain, (![F_292]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_292)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_292)) | ~m1_subset_1(F_292, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1372])).
% 5.96/2.35  tff(c_1385, plain, (![F_293]: (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_293)=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', F_293)) | ~m1_subset_1(F_293, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_1383])).
% 5.96/2.35  tff(c_201, plain, (![C_141, A_142, B_143]: (~v1_partfun1(C_141, A_142) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~v1_xboole_0(B_143) | v1_xboole_0(A_142))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.96/2.35  tff(c_211, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_201])).
% 5.96/2.35  tff(c_217, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_211])).
% 5.96/2.35  tff(c_218, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_217])).
% 5.96/2.35  tff(c_168, plain, (![A_135, B_136, C_137]: (k2_relset_1(A_135, B_136, C_137)=k2_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.96/2.35  tff(c_181, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_168])).
% 5.96/2.35  tff(c_232, plain, (![A_147, B_148, C_149]: (m1_subset_1(k2_relset_1(A_147, B_148, C_149), k1_zfmisc_1(B_148)) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.96/2.35  tff(c_258, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_181, c_232])).
% 5.96/2.35  tff(c_269, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_258])).
% 5.96/2.35  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.96/2.35  tff(c_275, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_269, c_2])).
% 5.96/2.35  tff(c_69, plain, (![C_114, A_115, B_116]: (v1_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.96/2.35  tff(c_82, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_69])).
% 5.96/2.35  tff(c_119, plain, (![C_126, A_127, B_128]: (v4_relat_1(C_126, A_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.96/2.35  tff(c_132, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_119])).
% 5.96/2.35  tff(c_145, plain, (![B_133, A_134]: (k1_relat_1(B_133)=A_134 | ~v1_partfun1(B_133, A_134) | ~v4_relat_1(B_133, A_134) | ~v1_relat_1(B_133))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.96/2.35  tff(c_148, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_132, c_145])).
% 5.96/2.35  tff(c_154, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_38, c_148])).
% 5.96/2.35  tff(c_333, plain, (![B_156, A_157]: (v1_funct_2(B_156, k1_relat_1(B_156), A_157) | ~r1_tarski(k2_relat_1(B_156), A_157) | ~v1_funct_1(B_156) | ~v1_relat_1(B_156))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.96/2.35  tff(c_336, plain, (![A_157]: (v1_funct_2('#skF_5', '#skF_1', A_157) | ~r1_tarski(k2_relat_1('#skF_5'), A_157) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_154, c_333])).
% 5.96/2.35  tff(c_339, plain, (![A_158]: (v1_funct_2('#skF_5', '#skF_1', A_158) | ~r1_tarski(k2_relat_1('#skF_5'), A_158))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_44, c_336])).
% 5.96/2.35  tff(c_343, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_275, c_339])).
% 5.96/2.35  tff(c_469, plain, (![A_170, B_171, C_172, D_173]: (m1_subset_1(k3_funct_2(A_170, B_171, C_172, D_173), B_171) | ~m1_subset_1(D_173, A_170) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))) | ~v1_funct_2(C_172, A_170, B_171) | ~v1_funct_1(C_172) | v1_xboole_0(A_170))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.96/2.35  tff(c_481, plain, (![D_173]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_173), '#skF_1') | ~m1_subset_1(D_173, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_469])).
% 5.96/2.35  tff(c_493, plain, (![D_173]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_173), '#skF_1') | ~m1_subset_1(D_173, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_481])).
% 5.96/2.35  tff(c_494, plain, (![D_173]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_173), '#skF_1') | ~m1_subset_1(D_173, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_493])).
% 5.96/2.35  tff(c_692, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_687, c_494])).
% 5.96/2.35  tff(c_696, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_692])).
% 5.96/2.35  tff(c_24, plain, (![A_25, B_26, C_27, D_28]: (k3_funct_2(A_25, B_26, C_27, D_28)=k1_funct_1(C_27, D_28) | ~m1_subset_1(D_28, A_25) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_2(C_27, A_25, B_26) | ~v1_funct_1(C_27) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.96/2.35  tff(c_699, plain, (![B_26, C_27]: (k3_funct_2('#skF_1', B_26, C_27, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_27, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_26))) | ~v1_funct_2(C_27, '#skF_1', B_26) | ~v1_funct_1(C_27) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_696, c_24])).
% 5.96/2.35  tff(c_961, plain, (![B_245, C_246]: (k3_funct_2('#skF_1', B_245, C_246, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_246, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_245))) | ~v1_funct_2(C_246, '#skF_1', B_245) | ~v1_funct_1(C_246))), inference(negUnitSimplification, [status(thm)], [c_54, c_699])).
% 5.96/2.35  tff(c_975, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_961])).
% 5.96/2.35  tff(c_983, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_343, c_975])).
% 5.96/2.35  tff(c_751, plain, (![A_203, B_204, C_205, D_206]: (k3_funct_2(A_203, B_204, C_205, D_206)=k7_partfun1(B_204, C_205, D_206) | ~m1_subset_1(D_206, A_203) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))) | ~v1_funct_2(C_205, A_203, B_204) | ~v1_funct_1(C_205) | v1_xboole_0(B_204) | v1_xboole_0(A_203))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.96/2.35  tff(c_753, plain, (![B_204, C_205]: (k3_funct_2('#skF_1', B_204, C_205, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_204, C_205, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_204))) | ~v1_funct_2(C_205, '#skF_1', B_204) | ~v1_funct_1(C_205) | v1_xboole_0(B_204) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_696, c_751])).
% 5.96/2.35  tff(c_1114, plain, (![B_265, C_266]: (k3_funct_2('#skF_1', B_265, C_266, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_265, C_266, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_265))) | ~v1_funct_2(C_266, '#skF_1', B_265) | ~v1_funct_1(C_266) | v1_xboole_0(B_265))), inference(negUnitSimplification, [status(thm)], [c_54, c_753])).
% 5.96/2.35  tff(c_1128, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1114])).
% 5.96/2.35  tff(c_1136, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_343, c_983, c_1128])).
% 5.96/2.35  tff(c_1137, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_218, c_1136])).
% 5.96/2.35  tff(c_36, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.96/2.35  tff(c_688, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_687, c_36])).
% 5.96/2.35  tff(c_1138, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1137, c_688])).
% 5.96/2.35  tff(c_1391, plain, (k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1385, c_1138])).
% 5.96/2.35  tff(c_1398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_687, c_1391])).
% 5.96/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.96/2.36  
% 5.96/2.36  Inference rules
% 5.96/2.36  ----------------------
% 5.96/2.36  #Ref     : 0
% 5.96/2.36  #Sup     : 281
% 5.96/2.36  #Fact    : 0
% 5.96/2.36  #Define  : 0
% 5.96/2.36  #Split   : 4
% 5.96/2.36  #Chain   : 0
% 5.96/2.36  #Close   : 0
% 5.96/2.36  
% 5.96/2.36  Ordering : KBO
% 5.96/2.36  
% 5.96/2.36  Simplification rules
% 5.96/2.36  ----------------------
% 5.96/2.36  #Subsume      : 38
% 5.96/2.36  #Demod        : 141
% 5.96/2.36  #Tautology    : 55
% 5.96/2.36  #SimpNegUnit  : 32
% 5.96/2.36  #BackRed      : 2
% 5.96/2.36  
% 5.96/2.36  #Partial instantiations: 0
% 5.96/2.36  #Strategies tried      : 1
% 5.96/2.36  
% 5.96/2.36  Timing (in seconds)
% 5.96/2.36  ----------------------
% 5.96/2.36  Preprocessing        : 0.59
% 5.96/2.36  Parsing              : 0.30
% 5.96/2.36  CNF conversion       : 0.06
% 5.96/2.36  Main loop            : 0.92
% 5.96/2.36  Inferencing          : 0.34
% 5.96/2.36  Reduction            : 0.28
% 5.96/2.36  Demodulation         : 0.19
% 5.96/2.36  BG Simplification    : 0.05
% 5.96/2.36  Subsumption          : 0.17
% 5.96/2.36  Abstraction          : 0.05
% 5.96/2.36  MUC search           : 0.00
% 5.96/2.36  Cooper               : 0.00
% 5.96/2.36  Total                : 1.59
% 5.96/2.36  Index Insertion      : 0.00
% 5.96/2.36  Index Deletion       : 0.00
% 5.96/2.36  Index Matching       : 0.00
% 5.96/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
