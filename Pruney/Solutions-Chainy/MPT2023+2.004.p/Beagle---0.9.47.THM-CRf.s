%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:12 EST 2020

% Result     : Theorem 28.72s
% Output     : CNFRefutation 28.93s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 758 expanded)
%              Number of leaves         :   40 ( 300 expanded)
%              Depth                    :   17
%              Number of atoms          :  320 (2850 expanded)
%              Number of equality atoms :    9 (  20 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_165,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(k9_yellow_6(A,B)))
                   => m1_subset_1(k3_xboole_0(C,D),u1_struct_0(k9_yellow_6(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_9)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => m1_connsp_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r2_hidden(C,u1_struct_0(k9_yellow_6(A,B)))
              <=> ( r2_hidden(B,C)
                  & v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_64,plain,(
    m1_subset_1('#skF_8',u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_96,plain,(
    ! [B_73,A_74] :
      ( v1_xboole_0(B_73)
      | ~ m1_subset_1(B_73,A_74)
      | ~ v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_111,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_64,c_96])).

tff(c_124,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_12,plain,(
    ! [D_15,A_10,B_11] :
      ( r2_hidden(D_15,k3_xboole_0(A_10,B_11))
      | ~ r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_72,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_70,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_193,plain,(
    ! [D_94,A_95,B_96] :
      ( r2_hidden(D_94,A_95)
      | ~ r2_hidden(D_94,k3_xboole_0(A_95,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91952,plain,(
    ! [A_1946,B_1947,B_1948] :
      ( r2_hidden('#skF_2'(k3_xboole_0(A_1946,B_1947),B_1948),A_1946)
      | r1_tarski(k3_xboole_0(A_1946,B_1947),B_1948) ) ),
    inference(resolution,[status(thm)],[c_10,c_193])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_92068,plain,(
    ! [A_1949,B_1950] : r1_tarski(k3_xboole_0(A_1949,B_1950),A_1949) ),
    inference(resolution,[status(thm)],[c_91952,c_8])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_92200,plain,(
    ! [A_1953,B_1954] : k3_xboole_0(k3_xboole_0(A_1953,B_1954),A_1953) = k3_xboole_0(A_1953,B_1954) ),
    inference(resolution,[status(thm)],[c_92068,c_30])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1207,plain,(
    ! [C_226,A_227,B_228] :
      ( m1_connsp_2(C_226,A_227,B_228)
      | ~ m1_subset_1(C_226,u1_struct_0(k9_yellow_6(A_227,B_228)))
      | ~ m1_subset_1(B_228,u1_struct_0(A_227))
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1238,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1207])).

tff(c_1251,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1238])).

tff(c_1252,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1251])).

tff(c_52,plain,(
    ! [C_39,A_36,B_37] :
      ( m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_connsp_2(C_39,A_36,B_37)
      | ~ m1_subset_1(B_37,u1_struct_0(A_36))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1258,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1252,c_52])).

tff(c_1261,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1258])).

tff(c_1262,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1261])).

tff(c_42,plain,(
    ! [A_23,B_24,C_25] :
      ( k9_subset_1(A_23,B_24,C_25) = k3_xboole_0(B_24,C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1602,plain,(
    ! [B_246] : k9_subset_1(u1_struct_0('#skF_5'),B_246,'#skF_7') = k3_xboole_0(B_246,'#skF_7') ),
    inference(resolution,[status(thm)],[c_1262,c_42])).

tff(c_40,plain,(
    ! [A_20,B_21,C_22] :
      ( m1_subset_1(k9_subset_1(A_20,B_21,C_22),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(C_22,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1611,plain,(
    ! [B_246] :
      ( m1_subset_1(k3_xboole_0(B_246,'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1602,c_40])).

tff(c_1617,plain,(
    ! [B_246] : m1_subset_1(k3_xboole_0(B_246,'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1262,c_1611])).

tff(c_92270,plain,(
    ! [B_1954] : m1_subset_1(k3_xboole_0('#skF_7',B_1954),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_92200,c_1617])).

tff(c_2843,plain,(
    ! [B_285,C_286,A_287] :
      ( v3_pre_topc(k3_xboole_0(B_285,C_286),A_287)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ v3_pre_topc(C_286,A_287)
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ v3_pre_topc(B_285,A_287)
      | ~ l1_pre_topc(A_287)
      | ~ v2_pre_topc(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2857,plain,(
    ! [B_285] :
      ( v3_pre_topc(k3_xboole_0(B_285,'#skF_7'),'#skF_5')
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_285,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1262,c_2843])).

tff(c_2902,plain,(
    ! [B_285] :
      ( v3_pre_topc(k3_xboole_0(B_285,'#skF_7'),'#skF_5')
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_285,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2857])).

tff(c_62539,plain,(
    ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2902])).

tff(c_34,plain,(
    ! [B_19,A_18] :
      ( r2_hidden(B_19,A_18)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2715,plain,(
    ! [C_282,A_283,B_284] :
      ( v3_pre_topc(C_282,A_283)
      | ~ r2_hidden(C_282,u1_struct_0(k9_yellow_6(A_283,B_284)))
      | ~ m1_subset_1(C_282,k1_zfmisc_1(u1_struct_0(A_283)))
      | ~ m1_subset_1(B_284,u1_struct_0(A_283))
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_91075,plain,(
    ! [B_1920,A_1921,B_1922] :
      ( v3_pre_topc(B_1920,A_1921)
      | ~ m1_subset_1(B_1920,k1_zfmisc_1(u1_struct_0(A_1921)))
      | ~ m1_subset_1(B_1922,u1_struct_0(A_1921))
      | ~ l1_pre_topc(A_1921)
      | ~ v2_pre_topc(A_1921)
      | v2_struct_0(A_1921)
      | ~ m1_subset_1(B_1920,u1_struct_0(k9_yellow_6(A_1921,B_1922)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1921,B_1922))) ) ),
    inference(resolution,[status(thm)],[c_34,c_2715])).

tff(c_91141,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_66,c_91075])).

tff(c_91163,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1262,c_91141])).

tff(c_91165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_74,c_62539,c_91163])).

tff(c_91167,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2902])).

tff(c_1241,plain,
    ( m1_connsp_2('#skF_8','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_1207])).

tff(c_1255,plain,
    ( m1_connsp_2('#skF_8','#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1241])).

tff(c_1256,plain,(
    m1_connsp_2('#skF_8','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1255])).

tff(c_1264,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1256,c_52])).

tff(c_1267,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1264])).

tff(c_1268,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1267])).

tff(c_2855,plain,(
    ! [B_285] :
      ( v3_pre_topc(k3_xboole_0(B_285,'#skF_8'),'#skF_5')
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_285,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1268,c_2843])).

tff(c_2899,plain,(
    ! [B_285] :
      ( v3_pre_topc(k3_xboole_0(B_285,'#skF_8'),'#skF_5')
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_285,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2855])).

tff(c_3250,plain,(
    ~ v3_pre_topc('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2899])).

tff(c_62339,plain,(
    ! [B_1364,A_1365,B_1366] :
      ( v3_pre_topc(B_1364,A_1365)
      | ~ m1_subset_1(B_1364,k1_zfmisc_1(u1_struct_0(A_1365)))
      | ~ m1_subset_1(B_1366,u1_struct_0(A_1365))
      | ~ l1_pre_topc(A_1365)
      | ~ v2_pre_topc(A_1365)
      | v2_struct_0(A_1365)
      | ~ m1_subset_1(B_1364,u1_struct_0(k9_yellow_6(A_1365,B_1366)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1365,B_1366))) ) ),
    inference(resolution,[status(thm)],[c_34,c_2715])).

tff(c_62428,plain,
    ( v3_pre_topc('#skF_8','#skF_5')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_64,c_62339])).

tff(c_62456,plain,
    ( v3_pre_topc('#skF_8','#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1268,c_62428])).

tff(c_62458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_74,c_3250,c_62456])).

tff(c_93028,plain,(
    ! [B_1965] :
      ( v3_pre_topc(k3_xboole_0(B_1965,'#skF_8'),'#skF_5')
      | ~ m1_subset_1(B_1965,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_1965,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_2899])).

tff(c_93055,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_7','#skF_8'),'#skF_5')
    | ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_1262,c_93028])).

tff(c_93102,plain,(
    v3_pre_topc(k3_xboole_0('#skF_7','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91167,c_93055])).

tff(c_91457,plain,(
    ! [C_1931,A_1932,B_1933] :
      ( r2_hidden(C_1931,u1_struct_0(k9_yellow_6(A_1932,B_1933)))
      | ~ v3_pre_topc(C_1931,A_1932)
      | ~ r2_hidden(B_1933,C_1931)
      | ~ m1_subset_1(C_1931,k1_zfmisc_1(u1_struct_0(A_1932)))
      | ~ m1_subset_1(B_1933,u1_struct_0(A_1932))
      | ~ l1_pre_topc(A_1932)
      | ~ v2_pre_topc(A_1932)
      | v2_struct_0(A_1932) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_46,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,B_29)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_119642,plain,(
    ! [C_2483,A_2484,B_2485] :
      ( m1_subset_1(C_2483,u1_struct_0(k9_yellow_6(A_2484,B_2485)))
      | ~ v3_pre_topc(C_2483,A_2484)
      | ~ r2_hidden(B_2485,C_2483)
      | ~ m1_subset_1(C_2483,k1_zfmisc_1(u1_struct_0(A_2484)))
      | ~ m1_subset_1(B_2485,u1_struct_0(A_2484))
      | ~ l1_pre_topc(A_2484)
      | ~ v2_pre_topc(A_2484)
      | v2_struct_0(A_2484) ) ),
    inference(resolution,[status(thm)],[c_91457,c_46])).

tff(c_62,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_7','#skF_8'),u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_119659,plain,
    ( ~ v3_pre_topc(k3_xboole_0('#skF_7','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_6',k3_xboole_0('#skF_7','#skF_8'))
    | ~ m1_subset_1(k3_xboole_0('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_119642,c_62])).

tff(c_119667,plain,
    ( ~ r2_hidden('#skF_6',k3_xboole_0('#skF_7','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_92270,c_93102,c_119659])).

tff(c_119668,plain,(
    ~ r2_hidden('#skF_6',k3_xboole_0('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_119667])).

tff(c_119687,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_119668])).

tff(c_119689,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_119687])).

tff(c_2217,plain,(
    ! [B_266,C_267,A_268] :
      ( r2_hidden(B_266,C_267)
      | ~ r2_hidden(C_267,u1_struct_0(k9_yellow_6(A_268,B_266)))
      | ~ m1_subset_1(C_267,k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ m1_subset_1(B_266,u1_struct_0(A_268))
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_120303,plain,(
    ! [B_2500,B_2501,A_2502] :
      ( r2_hidden(B_2500,B_2501)
      | ~ m1_subset_1(B_2501,k1_zfmisc_1(u1_struct_0(A_2502)))
      | ~ m1_subset_1(B_2500,u1_struct_0(A_2502))
      | ~ l1_pre_topc(A_2502)
      | ~ v2_pre_topc(A_2502)
      | v2_struct_0(A_2502)
      | ~ m1_subset_1(B_2501,u1_struct_0(k9_yellow_6(A_2502,B_2500)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_2502,B_2500))) ) ),
    inference(resolution,[status(thm)],[c_34,c_2217])).

tff(c_120377,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_66,c_120303])).

tff(c_120401,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1262,c_120377])).

tff(c_120403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_74,c_119689,c_120401])).

tff(c_120404,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_119687])).

tff(c_121133,plain,(
    ! [B_2513,B_2514,A_2515] :
      ( r2_hidden(B_2513,B_2514)
      | ~ m1_subset_1(B_2514,k1_zfmisc_1(u1_struct_0(A_2515)))
      | ~ m1_subset_1(B_2513,u1_struct_0(A_2515))
      | ~ l1_pre_topc(A_2515)
      | ~ v2_pre_topc(A_2515)
      | v2_struct_0(A_2515)
      | ~ m1_subset_1(B_2514,u1_struct_0(k9_yellow_6(A_2515,B_2513)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_2515,B_2513))) ) ),
    inference(resolution,[status(thm)],[c_34,c_2217])).

tff(c_121210,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_64,c_121133])).

tff(c_121235,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1268,c_121210])).

tff(c_121237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_74,c_120404,c_121235])).

tff(c_121239,plain,(
    v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_110,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_66,c_96])).

tff(c_121241,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121239,c_110])).

tff(c_121259,plain,(
    ! [A_2520,B_2521] :
      ( r2_hidden('#skF_2'(A_2520,B_2521),A_2520)
      | r1_tarski(A_2520,B_2521) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121306,plain,(
    ! [A_2527,B_2528] :
      ( ~ v1_xboole_0(A_2527)
      | r1_tarski(A_2527,B_2528) ) ),
    inference(resolution,[status(thm)],[c_121259,c_2])).

tff(c_121311,plain,(
    ! [A_2529,B_2530] :
      ( k3_xboole_0(A_2529,B_2530) = A_2529
      | ~ v1_xboole_0(A_2529) ) ),
    inference(resolution,[status(thm)],[c_121306,c_30])).

tff(c_121318,plain,(
    ! [B_2530] : k3_xboole_0('#skF_7',B_2530) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_121241,c_121311])).

tff(c_114,plain,(
    ! [B_75,A_76] :
      ( m1_subset_1(B_75,A_76)
      | ~ v1_xboole_0(B_75)
      | ~ v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_122,plain,
    ( ~ v1_xboole_0(k3_xboole_0('#skF_7','#skF_8'))
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_114,c_62])).

tff(c_121243,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121239,c_122])).

tff(c_121321,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121318,c_121243])).

tff(c_121325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121241,c_121321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.72/18.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.72/18.79  
% 28.72/18.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.72/18.79  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2
% 28.72/18.79  
% 28.72/18.79  %Foreground sorts:
% 28.72/18.79  
% 28.72/18.79  
% 28.72/18.79  %Background operators:
% 28.72/18.79  
% 28.72/18.79  
% 28.72/18.79  %Foreground operators:
% 28.72/18.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 28.72/18.79  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 28.72/18.79  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 28.72/18.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.72/18.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 28.72/18.79  tff('#skF_1', type, '#skF_1': $i > $i).
% 28.72/18.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 28.72/18.79  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 28.72/18.79  tff('#skF_7', type, '#skF_7': $i).
% 28.72/18.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 28.72/18.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 28.72/18.79  tff('#skF_5', type, '#skF_5': $i).
% 28.72/18.79  tff('#skF_6', type, '#skF_6': $i).
% 28.72/18.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 28.72/18.79  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 28.72/18.79  tff('#skF_8', type, '#skF_8': $i).
% 28.72/18.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.72/18.79  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 28.72/18.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.72/18.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 28.72/18.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 28.72/18.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 28.72/18.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 28.72/18.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 28.72/18.79  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 28.72/18.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 28.72/18.79  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 28.72/18.79  
% 28.93/18.81  tff(f_165, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k3_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_waybel_9)).
% 28.93/18.81  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 28.93/18.81  tff(f_47, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 28.93/18.81  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 28.93/18.81  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 28.93/18.81  tff(f_146, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_waybel_9)).
% 28.93/18.81  tff(f_112, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 28.93/18.81  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 28.93/18.81  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 28.93/18.81  tff(f_98, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_tops_1)).
% 28.93/18.81  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 28.93/18.81  tff(f_78, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 28.93/18.81  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 28.93/18.81  tff(c_64, plain, (m1_subset_1('#skF_8', u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 28.93/18.81  tff(c_96, plain, (![B_73, A_74]: (v1_xboole_0(B_73) | ~m1_subset_1(B_73, A_74) | ~v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_64])).
% 28.93/18.81  tff(c_111, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_64, c_96])).
% 28.93/18.81  tff(c_124, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_111])).
% 28.93/18.81  tff(c_74, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 28.93/18.81  tff(c_12, plain, (![D_15, A_10, B_11]: (r2_hidden(D_15, k3_xboole_0(A_10, B_11)) | ~r2_hidden(D_15, B_11) | ~r2_hidden(D_15, A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 28.93/18.81  tff(c_72, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 28.93/18.81  tff(c_70, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 28.93/18.81  tff(c_68, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 28.93/18.81  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 28.93/18.81  tff(c_193, plain, (![D_94, A_95, B_96]: (r2_hidden(D_94, A_95) | ~r2_hidden(D_94, k3_xboole_0(A_95, B_96)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 28.93/18.81  tff(c_91952, plain, (![A_1946, B_1947, B_1948]: (r2_hidden('#skF_2'(k3_xboole_0(A_1946, B_1947), B_1948), A_1946) | r1_tarski(k3_xboole_0(A_1946, B_1947), B_1948))), inference(resolution, [status(thm)], [c_10, c_193])).
% 28.93/18.81  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 28.93/18.81  tff(c_92068, plain, (![A_1949, B_1950]: (r1_tarski(k3_xboole_0(A_1949, B_1950), A_1949))), inference(resolution, [status(thm)], [c_91952, c_8])).
% 28.93/18.81  tff(c_30, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 28.93/18.81  tff(c_92200, plain, (![A_1953, B_1954]: (k3_xboole_0(k3_xboole_0(A_1953, B_1954), A_1953)=k3_xboole_0(A_1953, B_1954))), inference(resolution, [status(thm)], [c_92068, c_30])).
% 28.93/18.81  tff(c_66, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 28.93/18.81  tff(c_1207, plain, (![C_226, A_227, B_228]: (m1_connsp_2(C_226, A_227, B_228) | ~m1_subset_1(C_226, u1_struct_0(k9_yellow_6(A_227, B_228))) | ~m1_subset_1(B_228, u1_struct_0(A_227)) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227))), inference(cnfTransformation, [status(thm)], [f_146])).
% 28.93/18.81  tff(c_1238, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1207])).
% 28.93/18.81  tff(c_1251, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1238])).
% 28.93/18.81  tff(c_1252, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_74, c_1251])).
% 28.93/18.81  tff(c_52, plain, (![C_39, A_36, B_37]: (m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_connsp_2(C_39, A_36, B_37) | ~m1_subset_1(B_37, u1_struct_0(A_36)) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_112])).
% 28.93/18.81  tff(c_1258, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1252, c_52])).
% 28.93/18.81  tff(c_1261, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1258])).
% 28.93/18.81  tff(c_1262, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1261])).
% 28.93/18.81  tff(c_42, plain, (![A_23, B_24, C_25]: (k9_subset_1(A_23, B_24, C_25)=k3_xboole_0(B_24, C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 28.93/18.81  tff(c_1602, plain, (![B_246]: (k9_subset_1(u1_struct_0('#skF_5'), B_246, '#skF_7')=k3_xboole_0(B_246, '#skF_7'))), inference(resolution, [status(thm)], [c_1262, c_42])).
% 28.93/18.81  tff(c_40, plain, (![A_20, B_21, C_22]: (m1_subset_1(k9_subset_1(A_20, B_21, C_22), k1_zfmisc_1(A_20)) | ~m1_subset_1(C_22, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 28.93/18.81  tff(c_1611, plain, (![B_246]: (m1_subset_1(k3_xboole_0(B_246, '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_1602, c_40])).
% 28.93/18.81  tff(c_1617, plain, (![B_246]: (m1_subset_1(k3_xboole_0(B_246, '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_1262, c_1611])).
% 28.93/18.81  tff(c_92270, plain, (![B_1954]: (m1_subset_1(k3_xboole_0('#skF_7', B_1954), k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_92200, c_1617])).
% 28.93/18.81  tff(c_2843, plain, (![B_285, C_286, A_287]: (v3_pre_topc(k3_xboole_0(B_285, C_286), A_287) | ~m1_subset_1(C_286, k1_zfmisc_1(u1_struct_0(A_287))) | ~v3_pre_topc(C_286, A_287) | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_287))) | ~v3_pre_topc(B_285, A_287) | ~l1_pre_topc(A_287) | ~v2_pre_topc(A_287))), inference(cnfTransformation, [status(thm)], [f_98])).
% 28.93/18.81  tff(c_2857, plain, (![B_285]: (v3_pre_topc(k3_xboole_0(B_285, '#skF_7'), '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_285, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_1262, c_2843])).
% 28.93/18.81  tff(c_2902, plain, (![B_285]: (v3_pre_topc(k3_xboole_0(B_285, '#skF_7'), '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_285, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2857])).
% 28.93/18.81  tff(c_62539, plain, (~v3_pre_topc('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_2902])).
% 28.93/18.81  tff(c_34, plain, (![B_19, A_18]: (r2_hidden(B_19, A_18) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 28.93/18.81  tff(c_2715, plain, (![C_282, A_283, B_284]: (v3_pre_topc(C_282, A_283) | ~r2_hidden(C_282, u1_struct_0(k9_yellow_6(A_283, B_284))) | ~m1_subset_1(C_282, k1_zfmisc_1(u1_struct_0(A_283))) | ~m1_subset_1(B_284, u1_struct_0(A_283)) | ~l1_pre_topc(A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283))), inference(cnfTransformation, [status(thm)], [f_131])).
% 28.93/18.81  tff(c_91075, plain, (![B_1920, A_1921, B_1922]: (v3_pre_topc(B_1920, A_1921) | ~m1_subset_1(B_1920, k1_zfmisc_1(u1_struct_0(A_1921))) | ~m1_subset_1(B_1922, u1_struct_0(A_1921)) | ~l1_pre_topc(A_1921) | ~v2_pre_topc(A_1921) | v2_struct_0(A_1921) | ~m1_subset_1(B_1920, u1_struct_0(k9_yellow_6(A_1921, B_1922))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1921, B_1922))))), inference(resolution, [status(thm)], [c_34, c_2715])).
% 28.93/18.81  tff(c_91141, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_66, c_91075])).
% 28.93/18.81  tff(c_91163, plain, (v3_pre_topc('#skF_7', '#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1262, c_91141])).
% 28.93/18.81  tff(c_91165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_74, c_62539, c_91163])).
% 28.93/18.81  tff(c_91167, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_2902])).
% 28.93/18.81  tff(c_1241, plain, (m1_connsp_2('#skF_8', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_1207])).
% 28.93/18.81  tff(c_1255, plain, (m1_connsp_2('#skF_8', '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1241])).
% 28.93/18.81  tff(c_1256, plain, (m1_connsp_2('#skF_8', '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_74, c_1255])).
% 28.93/18.81  tff(c_1264, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1256, c_52])).
% 28.93/18.81  tff(c_1267, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1264])).
% 28.93/18.81  tff(c_1268, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1267])).
% 28.93/18.81  tff(c_2855, plain, (![B_285]: (v3_pre_topc(k3_xboole_0(B_285, '#skF_8'), '#skF_5') | ~v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_285, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_1268, c_2843])).
% 28.93/18.81  tff(c_2899, plain, (![B_285]: (v3_pre_topc(k3_xboole_0(B_285, '#skF_8'), '#skF_5') | ~v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_285, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2855])).
% 28.93/18.81  tff(c_3250, plain, (~v3_pre_topc('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_2899])).
% 28.93/18.81  tff(c_62339, plain, (![B_1364, A_1365, B_1366]: (v3_pre_topc(B_1364, A_1365) | ~m1_subset_1(B_1364, k1_zfmisc_1(u1_struct_0(A_1365))) | ~m1_subset_1(B_1366, u1_struct_0(A_1365)) | ~l1_pre_topc(A_1365) | ~v2_pre_topc(A_1365) | v2_struct_0(A_1365) | ~m1_subset_1(B_1364, u1_struct_0(k9_yellow_6(A_1365, B_1366))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1365, B_1366))))), inference(resolution, [status(thm)], [c_34, c_2715])).
% 28.93/18.81  tff(c_62428, plain, (v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_64, c_62339])).
% 28.93/18.81  tff(c_62456, plain, (v3_pre_topc('#skF_8', '#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1268, c_62428])).
% 28.93/18.81  tff(c_62458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_74, c_3250, c_62456])).
% 28.93/18.81  tff(c_93028, plain, (![B_1965]: (v3_pre_topc(k3_xboole_0(B_1965, '#skF_8'), '#skF_5') | ~m1_subset_1(B_1965, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_1965, '#skF_5'))), inference(splitRight, [status(thm)], [c_2899])).
% 28.93/18.81  tff(c_93055, plain, (v3_pre_topc(k3_xboole_0('#skF_7', '#skF_8'), '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_1262, c_93028])).
% 28.93/18.81  tff(c_93102, plain, (v3_pre_topc(k3_xboole_0('#skF_7', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_91167, c_93055])).
% 28.93/18.81  tff(c_91457, plain, (![C_1931, A_1932, B_1933]: (r2_hidden(C_1931, u1_struct_0(k9_yellow_6(A_1932, B_1933))) | ~v3_pre_topc(C_1931, A_1932) | ~r2_hidden(B_1933, C_1931) | ~m1_subset_1(C_1931, k1_zfmisc_1(u1_struct_0(A_1932))) | ~m1_subset_1(B_1933, u1_struct_0(A_1932)) | ~l1_pre_topc(A_1932) | ~v2_pre_topc(A_1932) | v2_struct_0(A_1932))), inference(cnfTransformation, [status(thm)], [f_131])).
% 28.93/18.81  tff(c_46, plain, (![A_28, B_29]: (m1_subset_1(A_28, B_29) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_78])).
% 28.93/18.81  tff(c_119642, plain, (![C_2483, A_2484, B_2485]: (m1_subset_1(C_2483, u1_struct_0(k9_yellow_6(A_2484, B_2485))) | ~v3_pre_topc(C_2483, A_2484) | ~r2_hidden(B_2485, C_2483) | ~m1_subset_1(C_2483, k1_zfmisc_1(u1_struct_0(A_2484))) | ~m1_subset_1(B_2485, u1_struct_0(A_2484)) | ~l1_pre_topc(A_2484) | ~v2_pre_topc(A_2484) | v2_struct_0(A_2484))), inference(resolution, [status(thm)], [c_91457, c_46])).
% 28.93/18.81  tff(c_62, plain, (~m1_subset_1(k3_xboole_0('#skF_7', '#skF_8'), u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 28.93/18.81  tff(c_119659, plain, (~v3_pre_topc(k3_xboole_0('#skF_7', '#skF_8'), '#skF_5') | ~r2_hidden('#skF_6', k3_xboole_0('#skF_7', '#skF_8')) | ~m1_subset_1(k3_xboole_0('#skF_7', '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_119642, c_62])).
% 28.93/18.81  tff(c_119667, plain, (~r2_hidden('#skF_6', k3_xboole_0('#skF_7', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_92270, c_93102, c_119659])).
% 28.93/18.81  tff(c_119668, plain, (~r2_hidden('#skF_6', k3_xboole_0('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_74, c_119667])).
% 28.93/18.81  tff(c_119687, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_12, c_119668])).
% 28.93/18.81  tff(c_119689, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_119687])).
% 28.93/18.81  tff(c_2217, plain, (![B_266, C_267, A_268]: (r2_hidden(B_266, C_267) | ~r2_hidden(C_267, u1_struct_0(k9_yellow_6(A_268, B_266))) | ~m1_subset_1(C_267, k1_zfmisc_1(u1_struct_0(A_268))) | ~m1_subset_1(B_266, u1_struct_0(A_268)) | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268))), inference(cnfTransformation, [status(thm)], [f_131])).
% 28.93/18.81  tff(c_120303, plain, (![B_2500, B_2501, A_2502]: (r2_hidden(B_2500, B_2501) | ~m1_subset_1(B_2501, k1_zfmisc_1(u1_struct_0(A_2502))) | ~m1_subset_1(B_2500, u1_struct_0(A_2502)) | ~l1_pre_topc(A_2502) | ~v2_pre_topc(A_2502) | v2_struct_0(A_2502) | ~m1_subset_1(B_2501, u1_struct_0(k9_yellow_6(A_2502, B_2500))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_2502, B_2500))))), inference(resolution, [status(thm)], [c_34, c_2217])).
% 28.93/18.81  tff(c_120377, plain, (r2_hidden('#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_66, c_120303])).
% 28.93/18.81  tff(c_120401, plain, (r2_hidden('#skF_6', '#skF_7') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1262, c_120377])).
% 28.93/18.81  tff(c_120403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_74, c_119689, c_120401])).
% 28.93/18.81  tff(c_120404, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_119687])).
% 28.93/18.81  tff(c_121133, plain, (![B_2513, B_2514, A_2515]: (r2_hidden(B_2513, B_2514) | ~m1_subset_1(B_2514, k1_zfmisc_1(u1_struct_0(A_2515))) | ~m1_subset_1(B_2513, u1_struct_0(A_2515)) | ~l1_pre_topc(A_2515) | ~v2_pre_topc(A_2515) | v2_struct_0(A_2515) | ~m1_subset_1(B_2514, u1_struct_0(k9_yellow_6(A_2515, B_2513))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_2515, B_2513))))), inference(resolution, [status(thm)], [c_34, c_2217])).
% 28.93/18.81  tff(c_121210, plain, (r2_hidden('#skF_6', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_64, c_121133])).
% 28.93/18.81  tff(c_121235, plain, (r2_hidden('#skF_6', '#skF_8') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1268, c_121210])).
% 28.93/18.81  tff(c_121237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_74, c_120404, c_121235])).
% 28.93/18.81  tff(c_121239, plain, (v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_111])).
% 28.93/18.81  tff(c_110, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_66, c_96])).
% 28.93/18.81  tff(c_121241, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_121239, c_110])).
% 28.93/18.81  tff(c_121259, plain, (![A_2520, B_2521]: (r2_hidden('#skF_2'(A_2520, B_2521), A_2520) | r1_tarski(A_2520, B_2521))), inference(cnfTransformation, [status(thm)], [f_38])).
% 28.93/18.81  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 28.93/18.81  tff(c_121306, plain, (![A_2527, B_2528]: (~v1_xboole_0(A_2527) | r1_tarski(A_2527, B_2528))), inference(resolution, [status(thm)], [c_121259, c_2])).
% 28.93/18.81  tff(c_121311, plain, (![A_2529, B_2530]: (k3_xboole_0(A_2529, B_2530)=A_2529 | ~v1_xboole_0(A_2529))), inference(resolution, [status(thm)], [c_121306, c_30])).
% 28.93/18.81  tff(c_121318, plain, (![B_2530]: (k3_xboole_0('#skF_7', B_2530)='#skF_7')), inference(resolution, [status(thm)], [c_121241, c_121311])).
% 28.93/18.81  tff(c_114, plain, (![B_75, A_76]: (m1_subset_1(B_75, A_76) | ~v1_xboole_0(B_75) | ~v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_64])).
% 28.93/18.81  tff(c_122, plain, (~v1_xboole_0(k3_xboole_0('#skF_7', '#skF_8')) | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_114, c_62])).
% 28.93/18.81  tff(c_121243, plain, (~v1_xboole_0(k3_xboole_0('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_121239, c_122])).
% 28.93/18.81  tff(c_121321, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_121318, c_121243])).
% 28.93/18.81  tff(c_121325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121241, c_121321])).
% 28.93/18.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.93/18.81  
% 28.93/18.81  Inference rules
% 28.93/18.81  ----------------------
% 28.93/18.81  #Ref     : 0
% 28.93/18.81  #Sup     : 30147
% 28.93/18.81  #Fact    : 0
% 28.93/18.81  #Define  : 0
% 28.93/18.81  #Split   : 66
% 28.93/18.81  #Chain   : 0
% 28.93/18.81  #Close   : 0
% 28.93/18.81  
% 28.93/18.81  Ordering : KBO
% 28.93/18.81  
% 28.93/18.81  Simplification rules
% 28.93/18.81  ----------------------
% 28.93/18.81  #Subsume      : 12420
% 28.93/18.81  #Demod        : 9014
% 28.93/18.81  #Tautology    : 4124
% 28.93/18.81  #SimpNegUnit  : 988
% 28.93/18.81  #BackRed      : 8
% 28.93/18.81  
% 28.93/18.81  #Partial instantiations: 0
% 28.93/18.81  #Strategies tried      : 1
% 28.93/18.81  
% 28.93/18.81  Timing (in seconds)
% 28.93/18.81  ----------------------
% 28.93/18.81  Preprocessing        : 0.38
% 28.93/18.81  Parsing              : 0.19
% 28.93/18.81  CNF conversion       : 0.03
% 28.93/18.81  Main loop            : 17.65
% 28.93/18.81  Inferencing          : 2.87
% 28.93/18.81  Reduction            : 5.67
% 28.93/18.81  Demodulation         : 4.37
% 28.93/18.81  BG Simplification    : 0.32
% 28.93/18.81  Subsumption          : 7.63
% 28.93/18.81  Abstraction          : 0.50
% 28.93/18.81  MUC search           : 0.00
% 28.93/18.81  Cooper               : 0.00
% 28.93/18.81  Total                : 18.07
% 28.93/18.81  Index Insertion      : 0.00
% 28.93/18.81  Index Deletion       : 0.00
% 28.93/18.81  Index Matching       : 0.00
% 28.93/18.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
