%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:13 EST 2020

% Result     : Theorem 46.41s
% Output     : CNFRefutation 46.61s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 780 expanded)
%              Number of leaves         :   38 ( 306 expanded)
%              Depth                    :   18
%              Number of atoms          :  349 (2979 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_164,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_9)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_145,axiom,(
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

tff(f_111,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_130,axiom,(
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

tff(f_67,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_62,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_96,plain,(
    ! [B_73,A_74] :
      ( v1_xboole_0(B_73)
      | ~ m1_subset_1(B_73,A_74)
      | ~ v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_115,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_62,c_96])).

tff(c_142,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_6,plain,(
    ! [D_10,A_5,B_6] :
      ( r2_hidden(D_10,k3_xboole_0(A_5,B_6))
      | ~ r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_449,plain,(
    ! [A_143,B_144,C_145] :
      ( r2_hidden('#skF_2'(A_143,B_144,C_145),B_144)
      | r2_hidden('#skF_3'(A_143,B_144,C_145),C_145)
      | k3_xboole_0(A_143,B_144) = C_145 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6,C_7),C_7)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k3_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_486,plain,(
    ! [A_143,B_144] :
      ( r2_hidden('#skF_3'(A_143,B_144,B_144),B_144)
      | k3_xboole_0(A_143,B_144) = B_144 ) ),
    inference(resolution,[status(thm)],[c_449,c_18])).

tff(c_22,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_2'(A_5,B_6,C_7),A_5)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k3_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_768,plain,(
    ! [A_177,B_178,C_179] :
      ( r2_hidden('#skF_2'(A_177,B_178,C_179),A_177)
      | ~ r2_hidden('#skF_3'(A_177,B_178,C_179),B_178)
      | ~ r2_hidden('#skF_3'(A_177,B_178,C_179),A_177)
      | k3_xboole_0(A_177,B_178) = C_179 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_191327,plain,(
    ! [A_6927,C_6928] :
      ( ~ r2_hidden('#skF_3'(A_6927,C_6928,C_6928),A_6927)
      | r2_hidden('#skF_2'(A_6927,C_6928,C_6928),A_6927)
      | k3_xboole_0(A_6927,C_6928) = C_6928 ) ),
    inference(resolution,[status(thm)],[c_22,c_768])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6,C_7),C_7)
      | ~ r2_hidden('#skF_3'(A_5,B_6,C_7),B_6)
      | ~ r2_hidden('#skF_3'(A_5,B_6,C_7),A_5)
      | k3_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_191381,plain,(
    ! [A_6929] :
      ( ~ r2_hidden('#skF_3'(A_6929,A_6929,A_6929),A_6929)
      | k3_xboole_0(A_6929,A_6929) = A_6929 ) ),
    inference(resolution,[status(thm)],[c_191327,c_12])).

tff(c_191431,plain,(
    ! [B_6930] : k3_xboole_0(B_6930,B_6930) = B_6930 ),
    inference(resolution,[status(thm)],[c_486,c_191381])).

tff(c_24,plain,(
    ! [A_11,B_12] : r1_tarski(k3_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_191655,plain,(
    ! [B_6930] : r1_tarski(B_6930,B_6930) ),
    inference(superposition,[status(thm),theory(equality)],[c_191431,c_24])).

tff(c_70,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_627,plain,(
    ! [C_163,A_164,B_165] :
      ( m1_connsp_2(C_163,A_164,B_165)
      | ~ m1_subset_1(C_163,u1_struct_0(k9_yellow_6(A_164,B_165)))
      | ~ m1_subset_1(B_165,u1_struct_0(A_164))
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_658,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_627])).

tff(c_671,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_658])).

tff(c_672,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_671])).

tff(c_50,plain,(
    ! [C_35,A_32,B_33] :
      ( m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_connsp_2(C_35,A_32,B_33)
      | ~ m1_subset_1(B_33,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_678,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_672,c_50])).

tff(c_681,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_678])).

tff(c_682,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_681])).

tff(c_42,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_698,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_682,c_42])).

tff(c_26,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_tarski(A_13,C_15)
      | ~ r1_tarski(B_14,C_15)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_749,plain,(
    ! [A_172] :
      ( r1_tarski(A_172,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_172,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_698,c_26])).

tff(c_1352,plain,(
    ! [A_207,A_208] :
      ( r1_tarski(A_207,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_207,A_208)
      | ~ r1_tarski(A_208,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_749,c_26])).

tff(c_1393,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k3_xboole_0(A_11,B_12),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_11,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_1352])).

tff(c_44,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1857,plain,(
    ! [B_255,C_256,A_257] :
      ( v3_pre_topc(k3_xboole_0(B_255,C_256),A_257)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ v3_pre_topc(C_256,A_257)
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ v3_pre_topc(B_255,A_257)
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1861,plain,(
    ! [B_255] :
      ( v3_pre_topc(k3_xboole_0(B_255,'#skF_6'),'#skF_4')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_255,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_682,c_1857])).

tff(c_1891,plain,(
    ! [B_255] :
      ( v3_pre_topc(k3_xboole_0(B_255,'#skF_6'),'#skF_4')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_255,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1861])).

tff(c_136993,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1891])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( r2_hidden(A_22,B_23)
      | v1_xboole_0(B_23)
      | ~ m1_subset_1(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1710,plain,(
    ! [C_237,A_238,B_239] :
      ( v3_pre_topc(C_237,A_238)
      | ~ r2_hidden(C_237,u1_struct_0(k9_yellow_6(A_238,B_239)))
      | ~ m1_subset_1(C_237,k1_zfmisc_1(u1_struct_0(A_238)))
      | ~ m1_subset_1(B_239,u1_struct_0(A_238))
      | ~ l1_pre_topc(A_238)
      | ~ v2_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_189280,plain,(
    ! [A_6787,A_6788,B_6789] :
      ( v3_pre_topc(A_6787,A_6788)
      | ~ m1_subset_1(A_6787,k1_zfmisc_1(u1_struct_0(A_6788)))
      | ~ m1_subset_1(B_6789,u1_struct_0(A_6788))
      | ~ l1_pre_topc(A_6788)
      | ~ v2_pre_topc(A_6788)
      | v2_struct_0(A_6788)
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_6788,B_6789)))
      | ~ m1_subset_1(A_6787,u1_struct_0(k9_yellow_6(A_6788,B_6789))) ) ),
    inference(resolution,[status(thm)],[c_40,c_1710])).

tff(c_189398,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_64,c_189280])).

tff(c_189433,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_682,c_189398])).

tff(c_189435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_72,c_136993,c_189433])).

tff(c_189437,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1891])).

tff(c_661,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_627])).

tff(c_675,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_661])).

tff(c_676,plain,(
    m1_connsp_2('#skF_7','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_675])).

tff(c_684,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_676,c_50])).

tff(c_687,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_684])).

tff(c_688,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_687])).

tff(c_1859,plain,(
    ! [B_255] :
      ( v3_pre_topc(k3_xboole_0(B_255,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_255,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_688,c_1857])).

tff(c_1888,plain,(
    ! [B_255] :
      ( v3_pre_topc(k3_xboole_0(B_255,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_255,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1859])).

tff(c_1917,plain,(
    ~ v3_pre_topc('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1888])).

tff(c_136356,plain,(
    ! [A_4940,A_4941,B_4942] :
      ( v3_pre_topc(A_4940,A_4941)
      | ~ m1_subset_1(A_4940,k1_zfmisc_1(u1_struct_0(A_4941)))
      | ~ m1_subset_1(B_4942,u1_struct_0(A_4941))
      | ~ l1_pre_topc(A_4941)
      | ~ v2_pre_topc(A_4941)
      | v2_struct_0(A_4941)
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_4941,B_4942)))
      | ~ m1_subset_1(A_4940,u1_struct_0(k9_yellow_6(A_4941,B_4942))) ) ),
    inference(resolution,[status(thm)],[c_40,c_1710])).

tff(c_136481,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_62,c_136356])).

tff(c_136518,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_688,c_136481])).

tff(c_136520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_72,c_1917,c_136518])).

tff(c_190699,plain,(
    ! [B_6878] :
      ( v3_pre_topc(k3_xboole_0(B_6878,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(B_6878,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_6878,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1888])).

tff(c_190725,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_682,c_190699])).

tff(c_190768,plain,(
    v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189437,c_190725])).

tff(c_136618,plain,(
    ! [C_4947,A_4948,B_4949] :
      ( r2_hidden(C_4947,u1_struct_0(k9_yellow_6(A_4948,B_4949)))
      | ~ v3_pre_topc(C_4947,A_4948)
      | ~ r2_hidden(B_4949,C_4947)
      | ~ m1_subset_1(C_4947,k1_zfmisc_1(u1_struct_0(A_4948)))
      | ~ m1_subset_1(B_4949,u1_struct_0(A_4948))
      | ~ l1_pre_topc(A_4948)
      | ~ v2_pre_topc(A_4948)
      | v2_struct_0(A_4948) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,B_21)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_242095,plain,(
    ! [C_8644,A_8645,B_8646] :
      ( m1_subset_1(C_8644,u1_struct_0(k9_yellow_6(A_8645,B_8646)))
      | ~ v3_pre_topc(C_8644,A_8645)
      | ~ r2_hidden(B_8646,C_8644)
      | ~ m1_subset_1(C_8644,k1_zfmisc_1(u1_struct_0(A_8645)))
      | ~ m1_subset_1(B_8646,u1_struct_0(A_8645))
      | ~ l1_pre_topc(A_8645)
      | ~ v2_pre_topc(A_8645)
      | v2_struct_0(A_8645) ) ),
    inference(resolution,[status(thm)],[c_136618,c_38])).

tff(c_60,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_242114,plain,
    ( ~ v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_242095,c_60])).

tff(c_242123,plain,
    ( ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_190768,c_242114])).

tff(c_242124,plain,
    ( ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_242123])).

tff(c_242125,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_242124])).

tff(c_242133,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_6','#skF_7'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_242125])).

tff(c_242139,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_1393,c_242133])).

tff(c_242159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_191655,c_242139])).

tff(c_242160,plain,(
    ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_242124])).

tff(c_242168,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_242160])).

tff(c_242170,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_242168])).

tff(c_1466,plain,(
    ! [B_215,C_216,A_217] :
      ( r2_hidden(B_215,C_216)
      | ~ r2_hidden(C_216,u1_struct_0(k9_yellow_6(A_217,B_215)))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ m1_subset_1(B_215,u1_struct_0(A_217))
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_242972,plain,(
    ! [B_8653,A_8654,A_8655] :
      ( r2_hidden(B_8653,A_8654)
      | ~ m1_subset_1(A_8654,k1_zfmisc_1(u1_struct_0(A_8655)))
      | ~ m1_subset_1(B_8653,u1_struct_0(A_8655))
      | ~ l1_pre_topc(A_8655)
      | ~ v2_pre_topc(A_8655)
      | v2_struct_0(A_8655)
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_8655,B_8653)))
      | ~ m1_subset_1(A_8654,u1_struct_0(k9_yellow_6(A_8655,B_8653))) ) ),
    inference(resolution,[status(thm)],[c_40,c_1466])).

tff(c_243090,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_64,c_242972])).

tff(c_243125,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_682,c_243090])).

tff(c_243127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_72,c_242170,c_243125])).

tff(c_243128,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_242168])).

tff(c_243323,plain,(
    ! [B_8657,A_8658,A_8659] :
      ( r2_hidden(B_8657,A_8658)
      | ~ m1_subset_1(A_8658,k1_zfmisc_1(u1_struct_0(A_8659)))
      | ~ m1_subset_1(B_8657,u1_struct_0(A_8659))
      | ~ l1_pre_topc(A_8659)
      | ~ v2_pre_topc(A_8659)
      | v2_struct_0(A_8659)
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_8659,B_8657)))
      | ~ m1_subset_1(A_8658,u1_struct_0(k9_yellow_6(A_8659,B_8657))) ) ),
    inference(resolution,[status(thm)],[c_40,c_1466])).

tff(c_243444,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_62,c_243323])).

tff(c_243480,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_688,c_243444])).

tff(c_243482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_72,c_243128,c_243480])).

tff(c_243484,plain,(
    v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_114,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_64,c_96])).

tff(c_243486,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243484,c_114])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_243495,plain,(
    ! [D_8663,A_8664,B_8665] :
      ( r2_hidden(D_8663,A_8664)
      | ~ r2_hidden(D_8663,k3_xboole_0(A_8664,B_8665)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_243592,plain,(
    ! [A_8694,B_8695] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_8694,B_8695)),A_8694)
      | v1_xboole_0(k3_xboole_0(A_8694,B_8695)) ) ),
    inference(resolution,[status(thm)],[c_4,c_243495])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_243614,plain,(
    ! [A_8696,B_8697] :
      ( ~ v1_xboole_0(A_8696)
      | v1_xboole_0(k3_xboole_0(A_8696,B_8697)) ) ),
    inference(resolution,[status(thm)],[c_243592,c_2])).

tff(c_128,plain,(
    ! [B_77,A_78] :
      ( m1_subset_1(B_77,A_78)
      | ~ v1_xboole_0(B_77)
      | ~ v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_141,plain,
    ( ~ v1_xboole_0(k3_xboole_0('#skF_6','#skF_7'))
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_128,c_60])).

tff(c_243488,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243484,c_141])).

tff(c_243617,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_243614,c_243488])).

tff(c_243621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_243486,c_243617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:26:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 46.41/34.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 46.41/34.69  
% 46.41/34.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 46.41/34.69  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 46.41/34.69  
% 46.41/34.69  %Foreground sorts:
% 46.41/34.69  
% 46.41/34.69  
% 46.41/34.69  %Background operators:
% 46.41/34.69  
% 46.41/34.69  
% 46.41/34.69  %Foreground operators:
% 46.41/34.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 46.41/34.69  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 46.41/34.69  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 46.41/34.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 46.41/34.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 46.41/34.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 46.41/34.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 46.41/34.69  tff('#skF_7', type, '#skF_7': $i).
% 46.41/34.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 46.41/34.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 46.41/34.69  tff('#skF_5', type, '#skF_5': $i).
% 46.41/34.69  tff('#skF_6', type, '#skF_6': $i).
% 46.41/34.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 46.41/34.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 46.41/34.69  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 46.41/34.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 46.41/34.69  tff('#skF_4', type, '#skF_4': $i).
% 46.41/34.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 46.41/34.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 46.41/34.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 46.41/34.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 46.41/34.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 46.41/34.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 46.41/34.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 46.41/34.69  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 46.41/34.69  
% 46.61/34.71  tff(f_164, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k3_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_waybel_9)).
% 46.61/34.71  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 46.61/34.71  tff(f_40, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 46.61/34.71  tff(f_42, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 46.61/34.71  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_waybel_9)).
% 46.61/34.71  tff(f_111, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 46.61/34.71  tff(f_77, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 46.61/34.71  tff(f_48, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 46.61/34.71  tff(f_97, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_tops_1)).
% 46.61/34.71  tff(f_73, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 46.61/34.71  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 46.61/34.71  tff(f_67, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 46.61/34.71  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 46.61/34.71  tff(c_62, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 46.61/34.71  tff(c_96, plain, (![B_73, A_74]: (v1_xboole_0(B_73) | ~m1_subset_1(B_73, A_74) | ~v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_61])).
% 46.61/34.71  tff(c_115, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_62, c_96])).
% 46.61/34.71  tff(c_142, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_115])).
% 46.61/34.71  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 46.61/34.71  tff(c_6, plain, (![D_10, A_5, B_6]: (r2_hidden(D_10, k3_xboole_0(A_5, B_6)) | ~r2_hidden(D_10, B_6) | ~r2_hidden(D_10, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 46.61/34.71  tff(c_449, plain, (![A_143, B_144, C_145]: (r2_hidden('#skF_2'(A_143, B_144, C_145), B_144) | r2_hidden('#skF_3'(A_143, B_144, C_145), C_145) | k3_xboole_0(A_143, B_144)=C_145)), inference(cnfTransformation, [status(thm)], [f_40])).
% 46.61/34.71  tff(c_18, plain, (![A_5, B_6, C_7]: (~r2_hidden('#skF_2'(A_5, B_6, C_7), C_7) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k3_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 46.61/34.71  tff(c_486, plain, (![A_143, B_144]: (r2_hidden('#skF_3'(A_143, B_144, B_144), B_144) | k3_xboole_0(A_143, B_144)=B_144)), inference(resolution, [status(thm)], [c_449, c_18])).
% 46.61/34.71  tff(c_22, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_2'(A_5, B_6, C_7), A_5) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k3_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 46.61/34.71  tff(c_768, plain, (![A_177, B_178, C_179]: (r2_hidden('#skF_2'(A_177, B_178, C_179), A_177) | ~r2_hidden('#skF_3'(A_177, B_178, C_179), B_178) | ~r2_hidden('#skF_3'(A_177, B_178, C_179), A_177) | k3_xboole_0(A_177, B_178)=C_179)), inference(cnfTransformation, [status(thm)], [f_40])).
% 46.61/34.71  tff(c_191327, plain, (![A_6927, C_6928]: (~r2_hidden('#skF_3'(A_6927, C_6928, C_6928), A_6927) | r2_hidden('#skF_2'(A_6927, C_6928, C_6928), A_6927) | k3_xboole_0(A_6927, C_6928)=C_6928)), inference(resolution, [status(thm)], [c_22, c_768])).
% 46.61/34.71  tff(c_12, plain, (![A_5, B_6, C_7]: (~r2_hidden('#skF_2'(A_5, B_6, C_7), C_7) | ~r2_hidden('#skF_3'(A_5, B_6, C_7), B_6) | ~r2_hidden('#skF_3'(A_5, B_6, C_7), A_5) | k3_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 46.61/34.71  tff(c_191381, plain, (![A_6929]: (~r2_hidden('#skF_3'(A_6929, A_6929, A_6929), A_6929) | k3_xboole_0(A_6929, A_6929)=A_6929)), inference(resolution, [status(thm)], [c_191327, c_12])).
% 46.61/34.71  tff(c_191431, plain, (![B_6930]: (k3_xboole_0(B_6930, B_6930)=B_6930)), inference(resolution, [status(thm)], [c_486, c_191381])).
% 46.61/34.71  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(k3_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 46.61/34.71  tff(c_191655, plain, (![B_6930]: (r1_tarski(B_6930, B_6930))), inference(superposition, [status(thm), theory('equality')], [c_191431, c_24])).
% 46.61/34.71  tff(c_70, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 46.61/34.71  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 46.61/34.71  tff(c_66, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 46.61/34.71  tff(c_64, plain, (m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 46.61/34.71  tff(c_627, plain, (![C_163, A_164, B_165]: (m1_connsp_2(C_163, A_164, B_165) | ~m1_subset_1(C_163, u1_struct_0(k9_yellow_6(A_164, B_165))) | ~m1_subset_1(B_165, u1_struct_0(A_164)) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_145])).
% 46.61/34.71  tff(c_658, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_627])).
% 46.61/34.71  tff(c_671, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_658])).
% 46.61/34.71  tff(c_672, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_671])).
% 46.61/34.71  tff(c_50, plain, (![C_35, A_32, B_33]: (m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_connsp_2(C_35, A_32, B_33) | ~m1_subset_1(B_33, u1_struct_0(A_32)) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_111])).
% 46.61/34.71  tff(c_678, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_672, c_50])).
% 46.61/34.71  tff(c_681, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_678])).
% 46.61/34.71  tff(c_682, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_72, c_681])).
% 46.61/34.71  tff(c_42, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 46.61/34.72  tff(c_698, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_682, c_42])).
% 46.61/34.72  tff(c_26, plain, (![A_13, C_15, B_14]: (r1_tarski(A_13, C_15) | ~r1_tarski(B_14, C_15) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 46.61/34.72  tff(c_749, plain, (![A_172]: (r1_tarski(A_172, u1_struct_0('#skF_4')) | ~r1_tarski(A_172, '#skF_6'))), inference(resolution, [status(thm)], [c_698, c_26])).
% 46.61/34.72  tff(c_1352, plain, (![A_207, A_208]: (r1_tarski(A_207, u1_struct_0('#skF_4')) | ~r1_tarski(A_207, A_208) | ~r1_tarski(A_208, '#skF_6'))), inference(resolution, [status(thm)], [c_749, c_26])).
% 46.61/34.72  tff(c_1393, plain, (![A_11, B_12]: (r1_tarski(k3_xboole_0(A_11, B_12), u1_struct_0('#skF_4')) | ~r1_tarski(A_11, '#skF_6'))), inference(resolution, [status(thm)], [c_24, c_1352])).
% 46.61/34.72  tff(c_44, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 46.61/34.72  tff(c_1857, plain, (![B_255, C_256, A_257]: (v3_pre_topc(k3_xboole_0(B_255, C_256), A_257) | ~m1_subset_1(C_256, k1_zfmisc_1(u1_struct_0(A_257))) | ~v3_pre_topc(C_256, A_257) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_257))) | ~v3_pre_topc(B_255, A_257) | ~l1_pre_topc(A_257) | ~v2_pre_topc(A_257))), inference(cnfTransformation, [status(thm)], [f_97])).
% 46.61/34.72  tff(c_1861, plain, (![B_255]: (v3_pre_topc(k3_xboole_0(B_255, '#skF_6'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_255, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_682, c_1857])).
% 46.61/34.72  tff(c_1891, plain, (![B_255]: (v3_pre_topc(k3_xboole_0(B_255, '#skF_6'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_255, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1861])).
% 46.61/34.72  tff(c_136993, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_1891])).
% 46.61/34.72  tff(c_40, plain, (![A_22, B_23]: (r2_hidden(A_22, B_23) | v1_xboole_0(B_23) | ~m1_subset_1(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 46.61/34.72  tff(c_1710, plain, (![C_237, A_238, B_239]: (v3_pre_topc(C_237, A_238) | ~r2_hidden(C_237, u1_struct_0(k9_yellow_6(A_238, B_239))) | ~m1_subset_1(C_237, k1_zfmisc_1(u1_struct_0(A_238))) | ~m1_subset_1(B_239, u1_struct_0(A_238)) | ~l1_pre_topc(A_238) | ~v2_pre_topc(A_238) | v2_struct_0(A_238))), inference(cnfTransformation, [status(thm)], [f_130])).
% 46.61/34.72  tff(c_189280, plain, (![A_6787, A_6788, B_6789]: (v3_pre_topc(A_6787, A_6788) | ~m1_subset_1(A_6787, k1_zfmisc_1(u1_struct_0(A_6788))) | ~m1_subset_1(B_6789, u1_struct_0(A_6788)) | ~l1_pre_topc(A_6788) | ~v2_pre_topc(A_6788) | v2_struct_0(A_6788) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_6788, B_6789))) | ~m1_subset_1(A_6787, u1_struct_0(k9_yellow_6(A_6788, B_6789))))), inference(resolution, [status(thm)], [c_40, c_1710])).
% 46.61/34.72  tff(c_189398, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_64, c_189280])).
% 46.61/34.72  tff(c_189433, plain, (v3_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_682, c_189398])).
% 46.61/34.72  tff(c_189435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_72, c_136993, c_189433])).
% 46.61/34.72  tff(c_189437, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_1891])).
% 46.61/34.72  tff(c_661, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_627])).
% 46.61/34.72  tff(c_675, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_661])).
% 46.61/34.72  tff(c_676, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_675])).
% 46.61/34.72  tff(c_684, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_676, c_50])).
% 46.61/34.72  tff(c_687, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_684])).
% 46.61/34.72  tff(c_688, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_72, c_687])).
% 46.61/34.72  tff(c_1859, plain, (![B_255]: (v3_pre_topc(k3_xboole_0(B_255, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_255, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_688, c_1857])).
% 46.61/34.72  tff(c_1888, plain, (![B_255]: (v3_pre_topc(k3_xboole_0(B_255, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_255, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1859])).
% 46.61/34.72  tff(c_1917, plain, (~v3_pre_topc('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_1888])).
% 46.61/34.72  tff(c_136356, plain, (![A_4940, A_4941, B_4942]: (v3_pre_topc(A_4940, A_4941) | ~m1_subset_1(A_4940, k1_zfmisc_1(u1_struct_0(A_4941))) | ~m1_subset_1(B_4942, u1_struct_0(A_4941)) | ~l1_pre_topc(A_4941) | ~v2_pre_topc(A_4941) | v2_struct_0(A_4941) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_4941, B_4942))) | ~m1_subset_1(A_4940, u1_struct_0(k9_yellow_6(A_4941, B_4942))))), inference(resolution, [status(thm)], [c_40, c_1710])).
% 46.61/34.72  tff(c_136481, plain, (v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_62, c_136356])).
% 46.61/34.72  tff(c_136518, plain, (v3_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_688, c_136481])).
% 46.61/34.72  tff(c_136520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_72, c_1917, c_136518])).
% 46.61/34.72  tff(c_190699, plain, (![B_6878]: (v3_pre_topc(k3_xboole_0(B_6878, '#skF_7'), '#skF_4') | ~m1_subset_1(B_6878, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_6878, '#skF_4'))), inference(splitRight, [status(thm)], [c_1888])).
% 46.61/34.72  tff(c_190725, plain, (v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_682, c_190699])).
% 46.61/34.72  tff(c_190768, plain, (v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_189437, c_190725])).
% 46.61/34.72  tff(c_136618, plain, (![C_4947, A_4948, B_4949]: (r2_hidden(C_4947, u1_struct_0(k9_yellow_6(A_4948, B_4949))) | ~v3_pre_topc(C_4947, A_4948) | ~r2_hidden(B_4949, C_4947) | ~m1_subset_1(C_4947, k1_zfmisc_1(u1_struct_0(A_4948))) | ~m1_subset_1(B_4949, u1_struct_0(A_4948)) | ~l1_pre_topc(A_4948) | ~v2_pre_topc(A_4948) | v2_struct_0(A_4948))), inference(cnfTransformation, [status(thm)], [f_130])).
% 46.61/34.72  tff(c_38, plain, (![A_20, B_21]: (m1_subset_1(A_20, B_21) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 46.61/34.72  tff(c_242095, plain, (![C_8644, A_8645, B_8646]: (m1_subset_1(C_8644, u1_struct_0(k9_yellow_6(A_8645, B_8646))) | ~v3_pre_topc(C_8644, A_8645) | ~r2_hidden(B_8646, C_8644) | ~m1_subset_1(C_8644, k1_zfmisc_1(u1_struct_0(A_8645))) | ~m1_subset_1(B_8646, u1_struct_0(A_8645)) | ~l1_pre_topc(A_8645) | ~v2_pre_topc(A_8645) | v2_struct_0(A_8645))), inference(resolution, [status(thm)], [c_136618, c_38])).
% 46.61/34.72  tff(c_60, plain, (~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 46.61/34.72  tff(c_242114, plain, (~v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_242095, c_60])).
% 46.61/34.72  tff(c_242123, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_190768, c_242114])).
% 46.61/34.72  tff(c_242124, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_72, c_242123])).
% 46.61/34.72  tff(c_242125, plain, (~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_242124])).
% 46.61/34.72  tff(c_242133, plain, (~r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_242125])).
% 46.61/34.72  tff(c_242139, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_1393, c_242133])).
% 46.61/34.72  tff(c_242159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_191655, c_242139])).
% 46.61/34.72  tff(c_242160, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_242124])).
% 46.61/34.72  tff(c_242168, plain, (~r2_hidden('#skF_5', '#skF_7') | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_242160])).
% 46.61/34.72  tff(c_242170, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_242168])).
% 46.61/34.72  tff(c_1466, plain, (![B_215, C_216, A_217]: (r2_hidden(B_215, C_216) | ~r2_hidden(C_216, u1_struct_0(k9_yellow_6(A_217, B_215))) | ~m1_subset_1(C_216, k1_zfmisc_1(u1_struct_0(A_217))) | ~m1_subset_1(B_215, u1_struct_0(A_217)) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_130])).
% 46.61/34.72  tff(c_242972, plain, (![B_8653, A_8654, A_8655]: (r2_hidden(B_8653, A_8654) | ~m1_subset_1(A_8654, k1_zfmisc_1(u1_struct_0(A_8655))) | ~m1_subset_1(B_8653, u1_struct_0(A_8655)) | ~l1_pre_topc(A_8655) | ~v2_pre_topc(A_8655) | v2_struct_0(A_8655) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_8655, B_8653))) | ~m1_subset_1(A_8654, u1_struct_0(k9_yellow_6(A_8655, B_8653))))), inference(resolution, [status(thm)], [c_40, c_1466])).
% 46.61/34.72  tff(c_243090, plain, (r2_hidden('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_64, c_242972])).
% 46.61/34.72  tff(c_243125, plain, (r2_hidden('#skF_5', '#skF_6') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_682, c_243090])).
% 46.61/34.72  tff(c_243127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_72, c_242170, c_243125])).
% 46.61/34.72  tff(c_243128, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_242168])).
% 46.61/34.72  tff(c_243323, plain, (![B_8657, A_8658, A_8659]: (r2_hidden(B_8657, A_8658) | ~m1_subset_1(A_8658, k1_zfmisc_1(u1_struct_0(A_8659))) | ~m1_subset_1(B_8657, u1_struct_0(A_8659)) | ~l1_pre_topc(A_8659) | ~v2_pre_topc(A_8659) | v2_struct_0(A_8659) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_8659, B_8657))) | ~m1_subset_1(A_8658, u1_struct_0(k9_yellow_6(A_8659, B_8657))))), inference(resolution, [status(thm)], [c_40, c_1466])).
% 46.61/34.72  tff(c_243444, plain, (r2_hidden('#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_62, c_243323])).
% 46.61/34.72  tff(c_243480, plain, (r2_hidden('#skF_5', '#skF_7') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_688, c_243444])).
% 46.61/34.72  tff(c_243482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_72, c_243128, c_243480])).
% 46.61/34.72  tff(c_243484, plain, (v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_115])).
% 46.61/34.72  tff(c_114, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_64, c_96])).
% 46.61/34.72  tff(c_243486, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_243484, c_114])).
% 46.61/34.72  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 46.61/34.72  tff(c_243495, plain, (![D_8663, A_8664, B_8665]: (r2_hidden(D_8663, A_8664) | ~r2_hidden(D_8663, k3_xboole_0(A_8664, B_8665)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 46.61/34.72  tff(c_243592, plain, (![A_8694, B_8695]: (r2_hidden('#skF_1'(k3_xboole_0(A_8694, B_8695)), A_8694) | v1_xboole_0(k3_xboole_0(A_8694, B_8695)))), inference(resolution, [status(thm)], [c_4, c_243495])).
% 46.61/34.72  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 46.61/34.72  tff(c_243614, plain, (![A_8696, B_8697]: (~v1_xboole_0(A_8696) | v1_xboole_0(k3_xboole_0(A_8696, B_8697)))), inference(resolution, [status(thm)], [c_243592, c_2])).
% 46.61/34.72  tff(c_128, plain, (![B_77, A_78]: (m1_subset_1(B_77, A_78) | ~v1_xboole_0(B_77) | ~v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_61])).
% 46.61/34.72  tff(c_141, plain, (~v1_xboole_0(k3_xboole_0('#skF_6', '#skF_7')) | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_128, c_60])).
% 46.61/34.72  tff(c_243488, plain, (~v1_xboole_0(k3_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_243484, c_141])).
% 46.61/34.72  tff(c_243617, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_243614, c_243488])).
% 46.61/34.72  tff(c_243621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_243486, c_243617])).
% 46.61/34.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 46.61/34.72  
% 46.61/34.72  Inference rules
% 46.61/34.72  ----------------------
% 46.61/34.72  #Ref     : 0
% 46.61/34.72  #Sup     : 58715
% 46.61/34.72  #Fact    : 0
% 46.61/34.72  #Define  : 0
% 46.61/34.72  #Split   : 68
% 46.61/34.72  #Chain   : 0
% 46.61/34.72  #Close   : 0
% 46.61/34.72  
% 46.61/34.72  Ordering : KBO
% 46.61/34.72  
% 46.61/34.72  Simplification rules
% 46.61/34.72  ----------------------
% 46.61/34.72  #Subsume      : 13601
% 46.61/34.72  #Demod        : 5097
% 46.61/34.72  #Tautology    : 4569
% 46.61/34.72  #SimpNegUnit  : 1626
% 46.61/34.72  #BackRed      : 990
% 46.61/34.72  
% 46.61/34.72  #Partial instantiations: 0
% 46.61/34.72  #Strategies tried      : 1
% 46.61/34.72  
% 46.61/34.72  Timing (in seconds)
% 46.61/34.72  ----------------------
% 46.61/34.72  Preprocessing        : 0.32
% 46.61/34.72  Parsing              : 0.17
% 46.61/34.72  CNF conversion       : 0.03
% 46.61/34.72  Main loop            : 33.64
% 46.61/34.72  Inferencing          : 5.67
% 46.61/34.72  Reduction            : 8.56
% 46.61/34.72  Demodulation         : 6.40
% 46.61/34.72  BG Simplification    : 0.76
% 46.61/34.72  Subsumption          : 16.02
% 46.61/34.72  Abstraction          : 1.08
% 46.61/34.72  MUC search           : 0.00
% 46.61/34.72  Cooper               : 0.00
% 46.61/34.72  Total                : 34.00
% 46.61/34.72  Index Insertion      : 0.00
% 46.61/34.72  Index Deletion       : 0.00
% 46.61/34.72  Index Matching       : 0.00
% 46.61/34.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
