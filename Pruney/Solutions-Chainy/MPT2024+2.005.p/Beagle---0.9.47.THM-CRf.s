%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:14 EST 2020

% Result     : Theorem 30.21s
% Output     : CNFRefutation 30.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 890 expanded)
%              Number of leaves         :   37 ( 353 expanded)
%              Depth                    :   17
%              Number of atoms          :  314 (3443 expanded)
%              Number of equality atoms :    5 (  13 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_175,negated_conjecture,(
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
                   => m1_subset_1(k2_xboole_0(C,D),u1_struct_0(k9_yellow_6(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).

tff(f_156,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => m1_connsp_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

tff(f_141,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_66,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_369,plain,(
    ! [C_145,A_146,B_147] :
      ( m1_connsp_2(C_145,A_146,B_147)
      | ~ m1_subset_1(C_145,u1_struct_0(k9_yellow_6(A_146,B_147)))
      | ~ m1_subset_1(B_147,u1_struct_0(A_146))
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_384,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_369])).

tff(c_393,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_384])).

tff(c_394,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_393])).

tff(c_44,plain,(
    ! [C_32,A_29,B_30] :
      ( m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_connsp_2(C_32,A_29,B_30)
      | ~ m1_subset_1(B_30,u1_struct_0(A_29))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_400,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_394,c_44])).

tff(c_403,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_400])).

tff(c_404,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_403])).

tff(c_2539,plain,(
    ! [C_198,B_199,A_200] :
      ( r2_hidden(C_198,B_199)
      | ~ m1_connsp_2(B_199,A_200,C_198)
      | ~ m1_subset_1(C_198,u1_struct_0(A_200))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200)
      | v2_struct_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2543,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_394,c_2539])).

tff(c_2550,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_404,c_62,c_2543])).

tff(c_2551,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2550])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( ~ r2_hidden(D_10,A_5)
      | r2_hidden(D_10,k2_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_387,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_369])).

tff(c_397,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_387])).

tff(c_398,plain,(
    m1_connsp_2('#skF_7','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_397])).

tff(c_406,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_398,c_44])).

tff(c_409,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_406])).

tff(c_410,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_409])).

tff(c_36,plain,(
    ! [A_18,B_19,C_20] :
      ( k4_subset_1(A_18,B_19,C_20) = k2_xboole_0(B_19,C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_537,plain,(
    ! [B_153] :
      ( k4_subset_1(u1_struct_0('#skF_4'),B_153,'#skF_7') = k2_xboole_0(B_153,'#skF_7')
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_410,c_36])).

tff(c_561,plain,(
    k4_subset_1(u1_struct_0('#skF_4'),'#skF_6','#skF_7') = k2_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_404,c_537])).

tff(c_34,plain,(
    ! [A_15,B_16,C_17] :
      ( m1_subset_1(k4_subset_1(A_15,B_16,C_17),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_609,plain,
    ( m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_34])).

tff(c_613,plain,(
    m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_410,c_609])).

tff(c_90,plain,(
    ! [B_73,A_74] :
      ( v1_xboole_0(B_73)
      | ~ m1_subset_1(B_73,A_74)
      | ~ v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_105,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_58,c_90])).

tff(c_117,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_3286,plain,(
    ! [B_216,C_217,A_218] :
      ( v3_pre_topc(k2_xboole_0(B_216,C_217),A_218)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ v3_pre_topc(C_217,A_218)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ v3_pre_topc(B_216,A_218)
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3314,plain,(
    ! [B_216] :
      ( v3_pre_topc(k2_xboole_0(B_216,'#skF_6'),'#skF_4')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_216,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_404,c_3286])).

tff(c_3368,plain,(
    ! [B_216] :
      ( v3_pre_topc(k2_xboole_0(B_216,'#skF_6'),'#skF_4')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_216,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3314])).

tff(c_3488,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3368])).

tff(c_28,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(B_14,A_13)
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2975,plain,(
    ! [C_208,A_209,B_210] :
      ( v3_pre_topc(C_208,A_209)
      | ~ r2_hidden(C_208,u1_struct_0(k9_yellow_6(A_209,B_210)))
      | ~ m1_subset_1(C_208,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ m1_subset_1(B_210,u1_struct_0(A_209))
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_32311,plain,(
    ! [B_681,A_682,B_683] :
      ( v3_pre_topc(B_681,A_682)
      | ~ m1_subset_1(B_681,k1_zfmisc_1(u1_struct_0(A_682)))
      | ~ m1_subset_1(B_683,u1_struct_0(A_682))
      | ~ l1_pre_topc(A_682)
      | ~ v2_pre_topc(A_682)
      | v2_struct_0(A_682)
      | ~ m1_subset_1(B_681,u1_struct_0(k9_yellow_6(A_682,B_683)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_682,B_683))) ) ),
    inference(resolution,[status(thm)],[c_28,c_2975])).

tff(c_32433,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_60,c_32311])).

tff(c_32469,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_404,c_32433])).

tff(c_32471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_68,c_3488,c_32469])).

tff(c_63385,plain,(
    ! [B_1140] :
      ( v3_pre_topc(k2_xboole_0(B_1140,'#skF_6'),'#skF_4')
      | ~ m1_subset_1(B_1140,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_1140,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_3368])).

tff(c_63454,plain,
    ( v3_pre_topc(k2_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_6'),'#skF_4')
    | ~ v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_613,c_63385])).

tff(c_63626,plain,(
    ~ v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_63454])).

tff(c_32473,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_3368])).

tff(c_3312,plain,(
    ! [B_216] :
      ( v3_pre_topc(k2_xboole_0(B_216,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_216,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_410,c_3286])).

tff(c_3365,plain,(
    ! [B_216] :
      ( v3_pre_topc(k2_xboole_0(B_216,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_216,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3312])).

tff(c_32478,plain,(
    ~ v3_pre_topc('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3365])).

tff(c_63223,plain,(
    ! [B_1137,A_1138,B_1139] :
      ( v3_pre_topc(B_1137,A_1138)
      | ~ m1_subset_1(B_1137,k1_zfmisc_1(u1_struct_0(A_1138)))
      | ~ m1_subset_1(B_1139,u1_struct_0(A_1138))
      | ~ l1_pre_topc(A_1138)
      | ~ v2_pre_topc(A_1138)
      | v2_struct_0(A_1138)
      | ~ m1_subset_1(B_1137,u1_struct_0(k9_yellow_6(A_1138,B_1139)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1138,B_1139))) ) ),
    inference(resolution,[status(thm)],[c_28,c_2975])).

tff(c_63344,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_58,c_63223])).

tff(c_63380,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_410,c_63344])).

tff(c_63382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_68,c_32478,c_63380])).

tff(c_65418,plain,(
    ! [B_1186] :
      ( v3_pre_topc(k2_xboole_0(B_1186,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(B_1186,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_1186,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_3365])).

tff(c_65466,plain,
    ( v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_404,c_65418])).

tff(c_65505,plain,(
    v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32473,c_65466])).

tff(c_65507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63626,c_65505])).

tff(c_65509,plain,(
    v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_63454])).

tff(c_3444,plain,(
    ! [C_220,A_221,B_222] :
      ( r2_hidden(C_220,u1_struct_0(k9_yellow_6(A_221,B_222)))
      | ~ v3_pre_topc(C_220,A_221)
      | ~ r2_hidden(B_222,C_220)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ m1_subset_1(B_222,u1_struct_0(A_221))
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_38,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,B_22)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_94005,plain,(
    ! [C_1630,A_1631,B_1632] :
      ( m1_subset_1(C_1630,u1_struct_0(k9_yellow_6(A_1631,B_1632)))
      | ~ v3_pre_topc(C_1630,A_1631)
      | ~ r2_hidden(B_1632,C_1630)
      | ~ m1_subset_1(C_1630,k1_zfmisc_1(u1_struct_0(A_1631)))
      | ~ m1_subset_1(B_1632,u1_struct_0(A_1631))
      | ~ l1_pre_topc(A_1631)
      | ~ v2_pre_topc(A_1631)
      | v2_struct_0(A_1631) ) ),
    inference(resolution,[status(thm)],[c_3444,c_38])).

tff(c_56,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_94022,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_94005,c_56])).

tff(c_94029,plain,
    ( ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_613,c_65509,c_94022])).

tff(c_94030,plain,(
    ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_94029])).

tff(c_94036,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_94030])).

tff(c_94046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2551,c_94036])).

tff(c_94047,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_94389,plain,(
    ! [C_1700,A_1701,B_1702] :
      ( m1_connsp_2(C_1700,A_1701,B_1702)
      | ~ m1_subset_1(C_1700,u1_struct_0(k9_yellow_6(A_1701,B_1702)))
      | ~ m1_subset_1(B_1702,u1_struct_0(A_1701))
      | ~ l1_pre_topc(A_1701)
      | ~ v2_pre_topc(A_1701)
      | v2_struct_0(A_1701) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_94411,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_94389])).

tff(c_94422,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_94411])).

tff(c_94423,plain,(
    m1_connsp_2('#skF_7','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_94422])).

tff(c_94431,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_94423,c_44])).

tff(c_94434,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_94431])).

tff(c_94435,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_94434])).

tff(c_94475,plain,(
    ! [C_1704,B_1705,A_1706] :
      ( r2_hidden(C_1704,B_1705)
      | ~ m1_connsp_2(B_1705,A_1706,C_1704)
      | ~ m1_subset_1(C_1704,u1_struct_0(A_1706))
      | ~ m1_subset_1(B_1705,k1_zfmisc_1(u1_struct_0(A_1706)))
      | ~ l1_pre_topc(A_1706)
      | ~ v2_pre_topc(A_1706)
      | v2_struct_0(A_1706) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_94477,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_94423,c_94475])).

tff(c_94482,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_94435,c_62,c_94477])).

tff(c_94483,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_94482])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94493,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_94483,c_2])).

tff(c_94498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94047,c_94493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.21/19.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.21/19.32  
% 30.21/19.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.21/19.32  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 30.21/19.32  
% 30.21/19.32  %Foreground sorts:
% 30.21/19.32  
% 30.21/19.32  
% 30.21/19.32  %Background operators:
% 30.21/19.32  
% 30.21/19.32  
% 30.21/19.32  %Foreground operators:
% 30.21/19.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 30.21/19.32  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 30.21/19.32  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 30.21/19.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.21/19.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.21/19.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 30.21/19.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 30.21/19.32  tff('#skF_7', type, '#skF_7': $i).
% 30.21/19.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 30.21/19.32  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 30.21/19.32  tff('#skF_5', type, '#skF_5': $i).
% 30.21/19.32  tff('#skF_6', type, '#skF_6': $i).
% 30.21/19.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 30.21/19.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 30.21/19.32  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 30.21/19.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.21/19.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 30.21/19.32  tff('#skF_4', type, '#skF_4': $i).
% 30.21/19.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 30.21/19.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.21/19.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 30.21/19.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 30.21/19.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 30.21/19.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 30.21/19.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 30.21/19.32  
% 30.21/19.34  tff(f_175, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k2_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_waybel_9)).
% 30.21/19.34  tff(f_156, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_waybel_9)).
% 30.21/19.34  tff(f_105, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 30.21/19.34  tff(f_122, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 30.21/19.34  tff(f_40, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 30.21/19.34  tff(f_67, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 30.21/19.34  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 30.21/19.34  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 30.21/19.34  tff(f_91, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_tops_1)).
% 30.21/19.34  tff(f_141, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 30.21/19.34  tff(f_71, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 30.21/19.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 30.21/19.34  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 30.21/19.34  tff(c_66, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 30.21/19.34  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 30.21/19.34  tff(c_62, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 30.21/19.34  tff(c_60, plain, (m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 30.21/19.34  tff(c_369, plain, (![C_145, A_146, B_147]: (m1_connsp_2(C_145, A_146, B_147) | ~m1_subset_1(C_145, u1_struct_0(k9_yellow_6(A_146, B_147))) | ~m1_subset_1(B_147, u1_struct_0(A_146)) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_156])).
% 30.21/19.34  tff(c_384, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_369])).
% 30.21/19.34  tff(c_393, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_384])).
% 30.21/19.34  tff(c_394, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_393])).
% 30.21/19.34  tff(c_44, plain, (![C_32, A_29, B_30]: (m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_connsp_2(C_32, A_29, B_30) | ~m1_subset_1(B_30, u1_struct_0(A_29)) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_105])).
% 30.21/19.34  tff(c_400, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_394, c_44])).
% 30.21/19.34  tff(c_403, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_400])).
% 30.21/19.34  tff(c_404, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_403])).
% 30.21/19.34  tff(c_2539, plain, (![C_198, B_199, A_200]: (r2_hidden(C_198, B_199) | ~m1_connsp_2(B_199, A_200, C_198) | ~m1_subset_1(C_198, u1_struct_0(A_200)) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200) | v2_struct_0(A_200))), inference(cnfTransformation, [status(thm)], [f_122])).
% 30.21/19.34  tff(c_2543, plain, (r2_hidden('#skF_5', '#skF_6') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_394, c_2539])).
% 30.21/19.34  tff(c_2550, plain, (r2_hidden('#skF_5', '#skF_6') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_404, c_62, c_2543])).
% 30.21/19.34  tff(c_2551, plain, (r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_2550])).
% 30.21/19.34  tff(c_10, plain, (![D_10, A_5, B_6]: (~r2_hidden(D_10, A_5) | r2_hidden(D_10, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 30.21/19.34  tff(c_58, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 30.21/19.34  tff(c_387, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_369])).
% 30.21/19.34  tff(c_397, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_387])).
% 30.21/19.34  tff(c_398, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_397])).
% 30.21/19.34  tff(c_406, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_398, c_44])).
% 30.21/19.34  tff(c_409, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_406])).
% 30.21/19.34  tff(c_410, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_409])).
% 30.21/19.34  tff(c_36, plain, (![A_18, B_19, C_20]: (k4_subset_1(A_18, B_19, C_20)=k2_xboole_0(B_19, C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 30.21/19.34  tff(c_537, plain, (![B_153]: (k4_subset_1(u1_struct_0('#skF_4'), B_153, '#skF_7')=k2_xboole_0(B_153, '#skF_7') | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_410, c_36])).
% 30.21/19.34  tff(c_561, plain, (k4_subset_1(u1_struct_0('#skF_4'), '#skF_6', '#skF_7')=k2_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_404, c_537])).
% 30.21/19.34  tff(c_34, plain, (![A_15, B_16, C_17]: (m1_subset_1(k4_subset_1(A_15, B_16, C_17), k1_zfmisc_1(A_15)) | ~m1_subset_1(C_17, k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 30.21/19.34  tff(c_609, plain, (m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_561, c_34])).
% 30.21/19.34  tff(c_613, plain, (m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_410, c_609])).
% 30.21/19.34  tff(c_90, plain, (![B_73, A_74]: (v1_xboole_0(B_73) | ~m1_subset_1(B_73, A_74) | ~v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_55])).
% 30.21/19.34  tff(c_105, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_58, c_90])).
% 30.21/19.34  tff(c_117, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_105])).
% 30.21/19.34  tff(c_3286, plain, (![B_216, C_217, A_218]: (v3_pre_topc(k2_xboole_0(B_216, C_217), A_218) | ~m1_subset_1(C_217, k1_zfmisc_1(u1_struct_0(A_218))) | ~v3_pre_topc(C_217, A_218) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_218))) | ~v3_pre_topc(B_216, A_218) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_91])).
% 30.21/19.34  tff(c_3314, plain, (![B_216]: (v3_pre_topc(k2_xboole_0(B_216, '#skF_6'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_216, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_404, c_3286])).
% 30.21/19.34  tff(c_3368, plain, (![B_216]: (v3_pre_topc(k2_xboole_0(B_216, '#skF_6'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_216, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3314])).
% 30.21/19.34  tff(c_3488, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_3368])).
% 30.21/19.34  tff(c_28, plain, (![B_14, A_13]: (r2_hidden(B_14, A_13) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 30.21/19.34  tff(c_2975, plain, (![C_208, A_209, B_210]: (v3_pre_topc(C_208, A_209) | ~r2_hidden(C_208, u1_struct_0(k9_yellow_6(A_209, B_210))) | ~m1_subset_1(C_208, k1_zfmisc_1(u1_struct_0(A_209))) | ~m1_subset_1(B_210, u1_struct_0(A_209)) | ~l1_pre_topc(A_209) | ~v2_pre_topc(A_209) | v2_struct_0(A_209))), inference(cnfTransformation, [status(thm)], [f_141])).
% 30.21/19.34  tff(c_32311, plain, (![B_681, A_682, B_683]: (v3_pre_topc(B_681, A_682) | ~m1_subset_1(B_681, k1_zfmisc_1(u1_struct_0(A_682))) | ~m1_subset_1(B_683, u1_struct_0(A_682)) | ~l1_pre_topc(A_682) | ~v2_pre_topc(A_682) | v2_struct_0(A_682) | ~m1_subset_1(B_681, u1_struct_0(k9_yellow_6(A_682, B_683))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_682, B_683))))), inference(resolution, [status(thm)], [c_28, c_2975])).
% 30.21/19.34  tff(c_32433, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_60, c_32311])).
% 30.21/19.34  tff(c_32469, plain, (v3_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_404, c_32433])).
% 30.21/19.34  tff(c_32471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_68, c_3488, c_32469])).
% 30.21/19.34  tff(c_63385, plain, (![B_1140]: (v3_pre_topc(k2_xboole_0(B_1140, '#skF_6'), '#skF_4') | ~m1_subset_1(B_1140, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_1140, '#skF_4'))), inference(splitRight, [status(thm)], [c_3368])).
% 30.21/19.34  tff(c_63454, plain, (v3_pre_topc(k2_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_6'), '#skF_4') | ~v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(resolution, [status(thm)], [c_613, c_63385])).
% 30.21/19.34  tff(c_63626, plain, (~v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(splitLeft, [status(thm)], [c_63454])).
% 30.21/19.34  tff(c_32473, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_3368])).
% 30.21/19.34  tff(c_3312, plain, (![B_216]: (v3_pre_topc(k2_xboole_0(B_216, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_216, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_410, c_3286])).
% 30.21/19.34  tff(c_3365, plain, (![B_216]: (v3_pre_topc(k2_xboole_0(B_216, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_216, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3312])).
% 30.21/19.34  tff(c_32478, plain, (~v3_pre_topc('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_3365])).
% 30.21/19.34  tff(c_63223, plain, (![B_1137, A_1138, B_1139]: (v3_pre_topc(B_1137, A_1138) | ~m1_subset_1(B_1137, k1_zfmisc_1(u1_struct_0(A_1138))) | ~m1_subset_1(B_1139, u1_struct_0(A_1138)) | ~l1_pre_topc(A_1138) | ~v2_pre_topc(A_1138) | v2_struct_0(A_1138) | ~m1_subset_1(B_1137, u1_struct_0(k9_yellow_6(A_1138, B_1139))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1138, B_1139))))), inference(resolution, [status(thm)], [c_28, c_2975])).
% 30.21/19.34  tff(c_63344, plain, (v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_58, c_63223])).
% 30.21/19.34  tff(c_63380, plain, (v3_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_410, c_63344])).
% 30.21/19.34  tff(c_63382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_68, c_32478, c_63380])).
% 30.21/19.34  tff(c_65418, plain, (![B_1186]: (v3_pre_topc(k2_xboole_0(B_1186, '#skF_7'), '#skF_4') | ~m1_subset_1(B_1186, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_1186, '#skF_4'))), inference(splitRight, [status(thm)], [c_3365])).
% 30.21/19.34  tff(c_65466, plain, (v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_404, c_65418])).
% 30.21/19.34  tff(c_65505, plain, (v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32473, c_65466])).
% 30.21/19.34  tff(c_65507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63626, c_65505])).
% 30.21/19.34  tff(c_65509, plain, (v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(splitRight, [status(thm)], [c_63454])).
% 30.21/19.34  tff(c_3444, plain, (![C_220, A_221, B_222]: (r2_hidden(C_220, u1_struct_0(k9_yellow_6(A_221, B_222))) | ~v3_pre_topc(C_220, A_221) | ~r2_hidden(B_222, C_220) | ~m1_subset_1(C_220, k1_zfmisc_1(u1_struct_0(A_221))) | ~m1_subset_1(B_222, u1_struct_0(A_221)) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | v2_struct_0(A_221))), inference(cnfTransformation, [status(thm)], [f_141])).
% 30.21/19.34  tff(c_38, plain, (![A_21, B_22]: (m1_subset_1(A_21, B_22) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 30.21/19.34  tff(c_94005, plain, (![C_1630, A_1631, B_1632]: (m1_subset_1(C_1630, u1_struct_0(k9_yellow_6(A_1631, B_1632))) | ~v3_pre_topc(C_1630, A_1631) | ~r2_hidden(B_1632, C_1630) | ~m1_subset_1(C_1630, k1_zfmisc_1(u1_struct_0(A_1631))) | ~m1_subset_1(B_1632, u1_struct_0(A_1631)) | ~l1_pre_topc(A_1631) | ~v2_pre_topc(A_1631) | v2_struct_0(A_1631))), inference(resolution, [status(thm)], [c_3444, c_38])).
% 30.21/19.34  tff(c_56, plain, (~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 30.21/19.34  tff(c_94022, plain, (~v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_94005, c_56])).
% 30.21/19.34  tff(c_94029, plain, (~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_613, c_65509, c_94022])).
% 30.21/19.34  tff(c_94030, plain, (~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_68, c_94029])).
% 30.21/19.34  tff(c_94036, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_10, c_94030])).
% 30.21/19.34  tff(c_94046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2551, c_94036])).
% 30.21/19.34  tff(c_94047, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_105])).
% 30.21/19.34  tff(c_94389, plain, (![C_1700, A_1701, B_1702]: (m1_connsp_2(C_1700, A_1701, B_1702) | ~m1_subset_1(C_1700, u1_struct_0(k9_yellow_6(A_1701, B_1702))) | ~m1_subset_1(B_1702, u1_struct_0(A_1701)) | ~l1_pre_topc(A_1701) | ~v2_pre_topc(A_1701) | v2_struct_0(A_1701))), inference(cnfTransformation, [status(thm)], [f_156])).
% 30.21/19.34  tff(c_94411, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_94389])).
% 30.21/19.34  tff(c_94422, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_94411])).
% 30.21/19.34  tff(c_94423, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_94422])).
% 30.21/19.34  tff(c_94431, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_94423, c_44])).
% 30.21/19.34  tff(c_94434, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_94431])).
% 30.21/19.34  tff(c_94435, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_94434])).
% 30.21/19.34  tff(c_94475, plain, (![C_1704, B_1705, A_1706]: (r2_hidden(C_1704, B_1705) | ~m1_connsp_2(B_1705, A_1706, C_1704) | ~m1_subset_1(C_1704, u1_struct_0(A_1706)) | ~m1_subset_1(B_1705, k1_zfmisc_1(u1_struct_0(A_1706))) | ~l1_pre_topc(A_1706) | ~v2_pre_topc(A_1706) | v2_struct_0(A_1706))), inference(cnfTransformation, [status(thm)], [f_122])).
% 30.21/19.34  tff(c_94477, plain, (r2_hidden('#skF_5', '#skF_7') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_94423, c_94475])).
% 30.21/19.34  tff(c_94482, plain, (r2_hidden('#skF_5', '#skF_7') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_94435, c_62, c_94477])).
% 30.21/19.34  tff(c_94483, plain, (r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_68, c_94482])).
% 30.21/19.34  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 30.21/19.34  tff(c_94493, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_94483, c_2])).
% 30.21/19.34  tff(c_94498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94047, c_94493])).
% 30.21/19.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.21/19.34  
% 30.21/19.34  Inference rules
% 30.21/19.34  ----------------------
% 30.21/19.34  #Ref     : 0
% 30.21/19.34  #Sup     : 21486
% 30.21/19.34  #Fact    : 36
% 30.21/19.34  #Define  : 0
% 30.21/19.34  #Split   : 71
% 30.21/19.34  #Chain   : 0
% 30.21/19.34  #Close   : 0
% 30.21/19.34  
% 30.21/19.34  Ordering : KBO
% 30.21/19.34  
% 30.21/19.34  Simplification rules
% 30.21/19.34  ----------------------
% 30.21/19.34  #Subsume      : 6952
% 30.21/19.34  #Demod        : 6276
% 30.21/19.34  #Tautology    : 1705
% 30.21/19.34  #SimpNegUnit  : 578
% 30.21/19.34  #BackRed      : 180
% 30.21/19.34  
% 30.21/19.34  #Partial instantiations: 0
% 30.21/19.34  #Strategies tried      : 1
% 30.21/19.34  
% 30.21/19.34  Timing (in seconds)
% 30.21/19.34  ----------------------
% 30.21/19.34  Preprocessing        : 0.35
% 30.21/19.34  Parsing              : 0.18
% 30.21/19.34  CNF conversion       : 0.03
% 30.21/19.34  Main loop            : 18.12
% 30.21/19.34  Inferencing          : 2.67
% 30.21/19.34  Reduction            : 5.10
% 30.21/19.34  Demodulation         : 4.03
% 30.21/19.34  BG Simplification    : 0.32
% 30.21/19.34  Subsumption          : 9.02
% 30.21/19.34  Abstraction          : 0.53
% 30.21/19.34  MUC search           : 0.00
% 30.21/19.34  Cooper               : 0.00
% 30.21/19.34  Total                : 18.51
% 30.21/19.34  Index Insertion      : 0.00
% 30.21/19.34  Index Deletion       : 0.00
% 30.21/19.34  Index Matching       : 0.00
% 30.21/19.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
