%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:44 EST 2020

% Result     : Theorem 8.77s
% Output     : CNFRefutation 8.77s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 398 expanded)
%              Number of leaves         :   35 ( 158 expanded)
%              Depth                    :   19
%              Number of atoms          :  355 (1981 expanded)
%              Number of equality atoms :   22 (  91 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k2_tsep_1 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( ( m1_pre_topc(B,D)
                        & m1_pre_topc(C,D) )
                     => ( r1_tsep_1(B,C)
                        | m1_pre_topc(k2_tsep_1(A,B,C),D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tmap_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k2_tsep_1(A,B,C))
        & v1_pre_topc(k2_tsep_1(A,B,C))
        & m1_pre_topc(k2_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_pre_topc(D)
                      & m1_pre_topc(D,A) )
                   => ( D = k2_tsep_1(A,B,C)
                    <=> u1_struct_0(D) = k3_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_58,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_81,plain,(
    ! [B_84,A_85] :
      ( l1_pre_topc(B_84)
      | ~ m1_pre_topc(B_84,A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_87,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_81])).

tff(c_102,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_87])).

tff(c_56,plain,(
    m1_pre_topc('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_54,plain,(
    m1_pre_topc('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_302,plain,(
    ! [A_112,B_113,C_114] :
      ( m1_pre_topc(k2_tsep_1(A_112,B_113,C_114),A_112)
      | ~ m1_pre_topc(C_114,A_112)
      | v2_struct_0(C_114)
      | ~ m1_pre_topc(B_113,A_112)
      | v2_struct_0(B_113)
      | ~ l1_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    ! [B_45,A_43] :
      ( l1_pre_topc(B_45)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_309,plain,(
    ! [A_112,B_113,C_114] :
      ( l1_pre_topc(k2_tsep_1(A_112,B_113,C_114))
      | ~ m1_pre_topc(C_114,A_112)
      | v2_struct_0(C_114)
      | ~ m1_pre_topc(B_113,A_112)
      | v2_struct_0(B_113)
      | ~ l1_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_302,c_34])).

tff(c_40,plain,(
    ! [A_61,B_62,C_63] :
      ( m1_pre_topc(k2_tsep_1(A_61,B_62,C_63),A_61)
      | ~ m1_pre_topc(C_63,A_61)
      | v2_struct_0(C_63)
      | ~ m1_pre_topc(B_62,A_61)
      | v2_struct_0(B_62)
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_22,plain,(
    ! [B_24,A_2] :
      ( r1_tarski(k2_struct_0(B_24),k2_struct_0(A_2))
      | ~ m1_pre_topc(B_24,A_2)
      | ~ l1_pre_topc(B_24)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_504,plain,(
    ! [A_137,B_138,C_139] :
      ( l1_pre_topc(k2_tsep_1(A_137,B_138,C_139))
      | ~ m1_pre_topc(C_139,A_137)
      | v2_struct_0(C_139)
      | ~ m1_pre_topc(B_138,A_137)
      | v2_struct_0(B_138)
      | ~ l1_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_302,c_34])).

tff(c_32,plain,(
    ! [A_42] :
      ( l1_struct_0(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_76,plain,(
    ! [A_83] :
      ( u1_struct_0(A_83) = k2_struct_0(A_83)
      | ~ l1_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_80,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_32,c_76])).

tff(c_508,plain,(
    ! [A_137,B_138,C_139] :
      ( u1_struct_0(k2_tsep_1(A_137,B_138,C_139)) = k2_struct_0(k2_tsep_1(A_137,B_138,C_139))
      | ~ m1_pre_topc(C_139,A_137)
      | v2_struct_0(C_139)
      | ~ m1_pre_topc(B_138,A_137)
      | v2_struct_0(B_138)
      | ~ l1_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_504,c_80])).

tff(c_52,plain,(
    ~ r1_tsep_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_66,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_84,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_81])).

tff(c_99,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_84])).

tff(c_112,plain,(
    ! [A_86] :
      ( u1_struct_0(A_86) = k2_struct_0(A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_32,c_76])).

tff(c_127,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_99,c_112])).

tff(c_62,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_96,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_81])).

tff(c_107,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_96])).

tff(c_125,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_107,c_112])).

tff(c_42,plain,(
    ! [A_61,B_62,C_63] :
      ( v1_pre_topc(k2_tsep_1(A_61,B_62,C_63))
      | ~ m1_pre_topc(C_63,A_61)
      | v2_struct_0(C_63)
      | ~ m1_pre_topc(B_62,A_61)
      | v2_struct_0(B_62)
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1357,plain,(
    ! [A_252,B_253,C_254] :
      ( u1_struct_0(k2_tsep_1(A_252,B_253,C_254)) = k3_xboole_0(u1_struct_0(B_253),u1_struct_0(C_254))
      | ~ m1_pre_topc(k2_tsep_1(A_252,B_253,C_254),A_252)
      | ~ v1_pre_topc(k2_tsep_1(A_252,B_253,C_254))
      | v2_struct_0(k2_tsep_1(A_252,B_253,C_254))
      | r1_tsep_1(B_253,C_254)
      | ~ m1_pre_topc(C_254,A_252)
      | v2_struct_0(C_254)
      | ~ m1_pre_topc(B_253,A_252)
      | v2_struct_0(B_253)
      | ~ l1_pre_topc(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1505,plain,(
    ! [A_266,B_267,C_268] :
      ( u1_struct_0(k2_tsep_1(A_266,B_267,C_268)) = k3_xboole_0(u1_struct_0(B_267),u1_struct_0(C_268))
      | ~ v1_pre_topc(k2_tsep_1(A_266,B_267,C_268))
      | v2_struct_0(k2_tsep_1(A_266,B_267,C_268))
      | r1_tsep_1(B_267,C_268)
      | ~ m1_pre_topc(C_268,A_266)
      | v2_struct_0(C_268)
      | ~ m1_pre_topc(B_267,A_266)
      | v2_struct_0(B_267)
      | ~ l1_pre_topc(A_266)
      | v2_struct_0(A_266) ) ),
    inference(resolution,[status(thm)],[c_40,c_1357])).

tff(c_44,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ v2_struct_0(k2_tsep_1(A_61,B_62,C_63))
      | ~ m1_pre_topc(C_63,A_61)
      | v2_struct_0(C_63)
      | ~ m1_pre_topc(B_62,A_61)
      | v2_struct_0(B_62)
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1726,plain,(
    ! [A_269,B_270,C_271] :
      ( u1_struct_0(k2_tsep_1(A_269,B_270,C_271)) = k3_xboole_0(u1_struct_0(B_270),u1_struct_0(C_271))
      | ~ v1_pre_topc(k2_tsep_1(A_269,B_270,C_271))
      | r1_tsep_1(B_270,C_271)
      | ~ m1_pre_topc(C_271,A_269)
      | v2_struct_0(C_271)
      | ~ m1_pre_topc(B_270,A_269)
      | v2_struct_0(B_270)
      | ~ l1_pre_topc(A_269)
      | v2_struct_0(A_269) ) ),
    inference(resolution,[status(thm)],[c_1505,c_44])).

tff(c_1730,plain,(
    ! [A_272,B_273,C_274] :
      ( u1_struct_0(k2_tsep_1(A_272,B_273,C_274)) = k3_xboole_0(u1_struct_0(B_273),u1_struct_0(C_274))
      | r1_tsep_1(B_273,C_274)
      | ~ m1_pre_topc(C_274,A_272)
      | v2_struct_0(C_274)
      | ~ m1_pre_topc(B_273,A_272)
      | v2_struct_0(B_273)
      | ~ l1_pre_topc(A_272)
      | v2_struct_0(A_272) ) ),
    inference(resolution,[status(thm)],[c_42,c_1726])).

tff(c_1936,plain,(
    ! [A_272,B_273] :
      ( u1_struct_0(k2_tsep_1(A_272,B_273,'#skF_6')) = k3_xboole_0(u1_struct_0(B_273),k2_struct_0('#skF_6'))
      | r1_tsep_1(B_273,'#skF_6')
      | ~ m1_pre_topc('#skF_6',A_272)
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc(B_273,A_272)
      | v2_struct_0(B_273)
      | ~ l1_pre_topc(A_272)
      | v2_struct_0(A_272) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_1730])).

tff(c_2413,plain,(
    ! [A_279,B_280] :
      ( u1_struct_0(k2_tsep_1(A_279,B_280,'#skF_6')) = k3_xboole_0(u1_struct_0(B_280),k2_struct_0('#skF_6'))
      | r1_tsep_1(B_280,'#skF_6')
      | ~ m1_pre_topc('#skF_6',A_279)
      | ~ m1_pre_topc(B_280,A_279)
      | v2_struct_0(B_280)
      | ~ l1_pre_topc(A_279)
      | v2_struct_0(A_279) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1936])).

tff(c_2629,plain,(
    ! [A_279] :
      ( u1_struct_0(k2_tsep_1(A_279,'#skF_5','#skF_6')) = k3_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6'))
      | r1_tsep_1('#skF_5','#skF_6')
      | ~ m1_pre_topc('#skF_6',A_279)
      | ~ m1_pre_topc('#skF_5',A_279)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_279)
      | v2_struct_0(A_279) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_2413])).

tff(c_2660,plain,(
    ! [A_281] :
      ( u1_struct_0(k2_tsep_1(A_281,'#skF_5','#skF_6')) = k3_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_6',A_281)
      | ~ m1_pre_topc('#skF_5',A_281)
      | ~ l1_pre_topc(A_281)
      | v2_struct_0(A_281) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_52,c_2629])).

tff(c_2849,plain,(
    ! [A_137] :
      ( k3_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) = k2_struct_0(k2_tsep_1(A_137,'#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_6',A_137)
      | ~ m1_pre_topc('#skF_5',A_137)
      | ~ l1_pre_topc(A_137)
      | v2_struct_0(A_137)
      | ~ m1_pre_topc('#skF_6',A_137)
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc('#skF_5',A_137)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_2660])).

tff(c_2867,plain,(
    ! [A_137] :
      ( k3_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) = k2_struct_0(k2_tsep_1(A_137,'#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_6',A_137)
      | ~ m1_pre_topc('#skF_5',A_137)
      | ~ l1_pre_topc(A_137)
      | v2_struct_0(A_137)
      | ~ m1_pre_topc('#skF_6',A_137)
      | ~ m1_pre_topc('#skF_5',A_137)
      | ~ l1_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_2849])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_72,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2655,plain,(
    ! [A_279] :
      ( u1_struct_0(k2_tsep_1(A_279,'#skF_5','#skF_6')) = k3_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_6',A_279)
      | ~ m1_pre_topc('#skF_5',A_279)
      | ~ l1_pre_topc(A_279)
      | v2_struct_0(A_279) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_52,c_2629])).

tff(c_126,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_102,c_112])).

tff(c_163,plain,(
    ! [B_92,C_93,A_94] :
      ( r1_tarski(u1_struct_0(B_92),u1_struct_0(C_93))
      | ~ m1_pre_topc(B_92,C_93)
      | ~ m1_pre_topc(C_93,A_94)
      | ~ m1_pre_topc(B_92,A_94)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_167,plain,(
    ! [B_92] :
      ( r1_tarski(u1_struct_0(B_92),u1_struct_0('#skF_7'))
      | ~ m1_pre_topc(B_92,'#skF_7')
      | ~ m1_pre_topc(B_92,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_163])).

tff(c_179,plain,(
    ! [B_92] :
      ( r1_tarski(u1_struct_0(B_92),k2_struct_0('#skF_7'))
      | ~ m1_pre_topc(B_92,'#skF_7')
      | ~ m1_pre_topc(B_92,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_126,c_167])).

tff(c_2823,plain,(
    ! [A_281] :
      ( r1_tarski(k3_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')),k2_struct_0('#skF_7'))
      | ~ m1_pre_topc(k2_tsep_1(A_281,'#skF_5','#skF_6'),'#skF_7')
      | ~ m1_pre_topc(k2_tsep_1(A_281,'#skF_5','#skF_6'),'#skF_4')
      | ~ m1_pre_topc('#skF_6',A_281)
      | ~ m1_pre_topc('#skF_5',A_281)
      | ~ l1_pre_topc(A_281)
      | v2_struct_0(A_281) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2660,c_179])).

tff(c_4889,plain,(
    r1_tarski(k3_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')),k2_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2823])).

tff(c_4892,plain,(
    ! [A_298] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_298,'#skF_5','#skF_6')),k2_struct_0('#skF_7'))
      | ~ m1_pre_topc('#skF_6',A_298)
      | ~ m1_pre_topc('#skF_5',A_298)
      | ~ l1_pre_topc(A_298)
      | v2_struct_0(A_298) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2655,c_4889])).

tff(c_146,plain,(
    ! [B_89,C_90,A_91] :
      ( m1_pre_topc(B_89,C_90)
      | ~ r1_tarski(u1_struct_0(B_89),u1_struct_0(C_90))
      | ~ m1_pre_topc(C_90,A_91)
      | ~ m1_pre_topc(B_89,A_91)
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_158,plain,(
    ! [B_89,A_91] :
      ( m1_pre_topc(B_89,'#skF_7')
      | ~ r1_tarski(u1_struct_0(B_89),k2_struct_0('#skF_7'))
      | ~ m1_pre_topc('#skF_7',A_91)
      | ~ m1_pre_topc(B_89,A_91)
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_146])).

tff(c_4938,plain,(
    ! [A_303,A_304] :
      ( m1_pre_topc(k2_tsep_1(A_303,'#skF_5','#skF_6'),'#skF_7')
      | ~ m1_pre_topc('#skF_7',A_304)
      | ~ m1_pre_topc(k2_tsep_1(A_303,'#skF_5','#skF_6'),A_304)
      | ~ l1_pre_topc(A_304)
      | ~ v2_pre_topc(A_304)
      | ~ m1_pre_topc('#skF_6',A_303)
      | ~ m1_pre_topc('#skF_5',A_303)
      | ~ l1_pre_topc(A_303)
      | v2_struct_0(A_303) ) ),
    inference(resolution,[status(thm)],[c_4892,c_158])).

tff(c_4941,plain,(
    ! [A_61] :
      ( m1_pre_topc(k2_tsep_1(A_61,'#skF_5','#skF_6'),'#skF_7')
      | ~ m1_pre_topc('#skF_7',A_61)
      | ~ v2_pre_topc(A_61)
      | ~ m1_pre_topc('#skF_6',A_61)
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc('#skF_5',A_61)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_40,c_4938])).

tff(c_4945,plain,(
    ! [A_305] :
      ( m1_pre_topc(k2_tsep_1(A_305,'#skF_5','#skF_6'),'#skF_7')
      | ~ m1_pre_topc('#skF_7',A_305)
      | ~ v2_pre_topc(A_305)
      | ~ m1_pre_topc('#skF_6',A_305)
      | ~ m1_pre_topc('#skF_5',A_305)
      | ~ l1_pre_topc(A_305)
      | v2_struct_0(A_305) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_4941])).

tff(c_50,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_4','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4955,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4945,c_50])).

tff(c_4967,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_62,c_72,c_58,c_4955])).

tff(c_4969,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4967])).

tff(c_4971,plain,(
    ~ r1_tarski(k3_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')),k2_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2823])).

tff(c_5095,plain,(
    ! [A_314] :
      ( ~ r1_tarski(k2_struct_0(k2_tsep_1(A_314,'#skF_5','#skF_6')),k2_struct_0('#skF_7'))
      | ~ m1_pre_topc('#skF_6',A_314)
      | ~ m1_pre_topc('#skF_5',A_314)
      | ~ l1_pre_topc(A_314)
      | v2_struct_0(A_314)
      | ~ m1_pre_topc('#skF_6',A_314)
      | ~ m1_pre_topc('#skF_5',A_314)
      | ~ l1_pre_topc(A_314)
      | v2_struct_0(A_314) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2867,c_4971])).

tff(c_5105,plain,(
    ! [A_314] :
      ( ~ m1_pre_topc('#skF_6',A_314)
      | ~ m1_pre_topc('#skF_5',A_314)
      | ~ l1_pre_topc(A_314)
      | v2_struct_0(A_314)
      | ~ m1_pre_topc(k2_tsep_1(A_314,'#skF_5','#skF_6'),'#skF_7')
      | ~ l1_pre_topc(k2_tsep_1(A_314,'#skF_5','#skF_6'))
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_22,c_5095])).

tff(c_5111,plain,(
    ! [A_315] :
      ( ~ m1_pre_topc('#skF_6',A_315)
      | ~ m1_pre_topc('#skF_5',A_315)
      | ~ l1_pre_topc(A_315)
      | v2_struct_0(A_315)
      | ~ m1_pre_topc(k2_tsep_1(A_315,'#skF_5','#skF_6'),'#skF_7')
      | ~ l1_pre_topc(k2_tsep_1(A_315,'#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_5105])).

tff(c_5115,plain,
    ( ~ l1_pre_topc(k2_tsep_1('#skF_7','#skF_5','#skF_6'))
    | ~ m1_pre_topc('#skF_6','#skF_7')
    | v2_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_7')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_5111])).

tff(c_5118,plain,
    ( ~ l1_pre_topc(k2_tsep_1('#skF_7','#skF_5','#skF_6'))
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_56,c_54,c_5115])).

tff(c_5119,plain,(
    ~ l1_pre_topc(k2_tsep_1('#skF_7','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_68,c_64,c_5118])).

tff(c_5122,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_7')
    | v2_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_7')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_309,c_5119])).

tff(c_5125,plain,
    ( v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_56,c_54,c_5122])).

tff(c_5127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_68,c_64,c_5125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.77/3.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.77/3.05  
% 8.77/3.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.77/3.05  %$ r2_hidden > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k2_tsep_1 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 8.77/3.05  
% 8.77/3.05  %Foreground sorts:
% 8.77/3.05  
% 8.77/3.05  
% 8.77/3.05  %Background operators:
% 8.77/3.05  
% 8.77/3.05  
% 8.77/3.05  %Foreground operators:
% 8.77/3.05  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.77/3.05  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.77/3.05  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 8.77/3.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.77/3.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.77/3.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.77/3.05  tff('#skF_7', type, '#skF_7': $i).
% 8.77/3.05  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.77/3.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.77/3.05  tff('#skF_5', type, '#skF_5': $i).
% 8.77/3.05  tff('#skF_6', type, '#skF_6': $i).
% 8.77/3.05  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.77/3.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.77/3.05  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.77/3.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.77/3.05  tff('#skF_4', type, '#skF_4': $i).
% 8.77/3.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.77/3.05  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.77/3.05  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.77/3.05  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 8.77/3.05  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.77/3.05  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 8.77/3.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.77/3.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.77/3.05  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.77/3.05  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.77/3.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.77/3.05  
% 8.77/3.07  tff(f_163, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, D)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tmap_1)).
% 8.77/3.07  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.77/3.07  tff(f_115, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 8.77/3.07  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 8.77/3.07  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.77/3.07  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 8.77/3.07  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k2_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k3_xboole_0(u1_struct_0(B), u1_struct_0(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tsep_1)).
% 8.77/3.07  tff(f_129, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 8.77/3.07  tff(c_60, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.07  tff(c_68, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.07  tff(c_64, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.07  tff(c_70, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.07  tff(c_58, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.07  tff(c_81, plain, (![B_84, A_85]: (l1_pre_topc(B_84) | ~m1_pre_topc(B_84, A_85) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.77/3.07  tff(c_87, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_81])).
% 8.77/3.07  tff(c_102, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_87])).
% 8.77/3.07  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.07  tff(c_54, plain, (m1_pre_topc('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.07  tff(c_302, plain, (![A_112, B_113, C_114]: (m1_pre_topc(k2_tsep_1(A_112, B_113, C_114), A_112) | ~m1_pre_topc(C_114, A_112) | v2_struct_0(C_114) | ~m1_pre_topc(B_113, A_112) | v2_struct_0(B_113) | ~l1_pre_topc(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.77/3.07  tff(c_34, plain, (![B_45, A_43]: (l1_pre_topc(B_45) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.77/3.07  tff(c_309, plain, (![A_112, B_113, C_114]: (l1_pre_topc(k2_tsep_1(A_112, B_113, C_114)) | ~m1_pre_topc(C_114, A_112) | v2_struct_0(C_114) | ~m1_pre_topc(B_113, A_112) | v2_struct_0(B_113) | ~l1_pre_topc(A_112) | v2_struct_0(A_112))), inference(resolution, [status(thm)], [c_302, c_34])).
% 8.77/3.07  tff(c_40, plain, (![A_61, B_62, C_63]: (m1_pre_topc(k2_tsep_1(A_61, B_62, C_63), A_61) | ~m1_pre_topc(C_63, A_61) | v2_struct_0(C_63) | ~m1_pre_topc(B_62, A_61) | v2_struct_0(B_62) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.77/3.07  tff(c_22, plain, (![B_24, A_2]: (r1_tarski(k2_struct_0(B_24), k2_struct_0(A_2)) | ~m1_pre_topc(B_24, A_2) | ~l1_pre_topc(B_24) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.77/3.07  tff(c_504, plain, (![A_137, B_138, C_139]: (l1_pre_topc(k2_tsep_1(A_137, B_138, C_139)) | ~m1_pre_topc(C_139, A_137) | v2_struct_0(C_139) | ~m1_pre_topc(B_138, A_137) | v2_struct_0(B_138) | ~l1_pre_topc(A_137) | v2_struct_0(A_137))), inference(resolution, [status(thm)], [c_302, c_34])).
% 8.77/3.07  tff(c_32, plain, (![A_42]: (l1_struct_0(A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.77/3.07  tff(c_76, plain, (![A_83]: (u1_struct_0(A_83)=k2_struct_0(A_83) | ~l1_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.77/3.07  tff(c_80, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_32, c_76])).
% 8.77/3.07  tff(c_508, plain, (![A_137, B_138, C_139]: (u1_struct_0(k2_tsep_1(A_137, B_138, C_139))=k2_struct_0(k2_tsep_1(A_137, B_138, C_139)) | ~m1_pre_topc(C_139, A_137) | v2_struct_0(C_139) | ~m1_pre_topc(B_138, A_137) | v2_struct_0(B_138) | ~l1_pre_topc(A_137) | v2_struct_0(A_137))), inference(resolution, [status(thm)], [c_504, c_80])).
% 8.77/3.07  tff(c_52, plain, (~r1_tsep_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.07  tff(c_66, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.07  tff(c_84, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_81])).
% 8.77/3.07  tff(c_99, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_84])).
% 8.77/3.07  tff(c_112, plain, (![A_86]: (u1_struct_0(A_86)=k2_struct_0(A_86) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_32, c_76])).
% 8.77/3.07  tff(c_127, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_99, c_112])).
% 8.77/3.07  tff(c_62, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.07  tff(c_96, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_62, c_81])).
% 8.77/3.07  tff(c_107, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_96])).
% 8.77/3.07  tff(c_125, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_107, c_112])).
% 8.77/3.07  tff(c_42, plain, (![A_61, B_62, C_63]: (v1_pre_topc(k2_tsep_1(A_61, B_62, C_63)) | ~m1_pre_topc(C_63, A_61) | v2_struct_0(C_63) | ~m1_pre_topc(B_62, A_61) | v2_struct_0(B_62) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.77/3.07  tff(c_1357, plain, (![A_252, B_253, C_254]: (u1_struct_0(k2_tsep_1(A_252, B_253, C_254))=k3_xboole_0(u1_struct_0(B_253), u1_struct_0(C_254)) | ~m1_pre_topc(k2_tsep_1(A_252, B_253, C_254), A_252) | ~v1_pre_topc(k2_tsep_1(A_252, B_253, C_254)) | v2_struct_0(k2_tsep_1(A_252, B_253, C_254)) | r1_tsep_1(B_253, C_254) | ~m1_pre_topc(C_254, A_252) | v2_struct_0(C_254) | ~m1_pre_topc(B_253, A_252) | v2_struct_0(B_253) | ~l1_pre_topc(A_252) | v2_struct_0(A_252))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.77/3.07  tff(c_1505, plain, (![A_266, B_267, C_268]: (u1_struct_0(k2_tsep_1(A_266, B_267, C_268))=k3_xboole_0(u1_struct_0(B_267), u1_struct_0(C_268)) | ~v1_pre_topc(k2_tsep_1(A_266, B_267, C_268)) | v2_struct_0(k2_tsep_1(A_266, B_267, C_268)) | r1_tsep_1(B_267, C_268) | ~m1_pre_topc(C_268, A_266) | v2_struct_0(C_268) | ~m1_pre_topc(B_267, A_266) | v2_struct_0(B_267) | ~l1_pre_topc(A_266) | v2_struct_0(A_266))), inference(resolution, [status(thm)], [c_40, c_1357])).
% 8.77/3.07  tff(c_44, plain, (![A_61, B_62, C_63]: (~v2_struct_0(k2_tsep_1(A_61, B_62, C_63)) | ~m1_pre_topc(C_63, A_61) | v2_struct_0(C_63) | ~m1_pre_topc(B_62, A_61) | v2_struct_0(B_62) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.77/3.07  tff(c_1726, plain, (![A_269, B_270, C_271]: (u1_struct_0(k2_tsep_1(A_269, B_270, C_271))=k3_xboole_0(u1_struct_0(B_270), u1_struct_0(C_271)) | ~v1_pre_topc(k2_tsep_1(A_269, B_270, C_271)) | r1_tsep_1(B_270, C_271) | ~m1_pre_topc(C_271, A_269) | v2_struct_0(C_271) | ~m1_pre_topc(B_270, A_269) | v2_struct_0(B_270) | ~l1_pre_topc(A_269) | v2_struct_0(A_269))), inference(resolution, [status(thm)], [c_1505, c_44])).
% 8.77/3.07  tff(c_1730, plain, (![A_272, B_273, C_274]: (u1_struct_0(k2_tsep_1(A_272, B_273, C_274))=k3_xboole_0(u1_struct_0(B_273), u1_struct_0(C_274)) | r1_tsep_1(B_273, C_274) | ~m1_pre_topc(C_274, A_272) | v2_struct_0(C_274) | ~m1_pre_topc(B_273, A_272) | v2_struct_0(B_273) | ~l1_pre_topc(A_272) | v2_struct_0(A_272))), inference(resolution, [status(thm)], [c_42, c_1726])).
% 8.77/3.07  tff(c_1936, plain, (![A_272, B_273]: (u1_struct_0(k2_tsep_1(A_272, B_273, '#skF_6'))=k3_xboole_0(u1_struct_0(B_273), k2_struct_0('#skF_6')) | r1_tsep_1(B_273, '#skF_6') | ~m1_pre_topc('#skF_6', A_272) | v2_struct_0('#skF_6') | ~m1_pre_topc(B_273, A_272) | v2_struct_0(B_273) | ~l1_pre_topc(A_272) | v2_struct_0(A_272))), inference(superposition, [status(thm), theory('equality')], [c_125, c_1730])).
% 8.77/3.07  tff(c_2413, plain, (![A_279, B_280]: (u1_struct_0(k2_tsep_1(A_279, B_280, '#skF_6'))=k3_xboole_0(u1_struct_0(B_280), k2_struct_0('#skF_6')) | r1_tsep_1(B_280, '#skF_6') | ~m1_pre_topc('#skF_6', A_279) | ~m1_pre_topc(B_280, A_279) | v2_struct_0(B_280) | ~l1_pre_topc(A_279) | v2_struct_0(A_279))), inference(negUnitSimplification, [status(thm)], [c_64, c_1936])).
% 8.77/3.07  tff(c_2629, plain, (![A_279]: (u1_struct_0(k2_tsep_1(A_279, '#skF_5', '#skF_6'))=k3_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6')) | r1_tsep_1('#skF_5', '#skF_6') | ~m1_pre_topc('#skF_6', A_279) | ~m1_pre_topc('#skF_5', A_279) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_279) | v2_struct_0(A_279))), inference(superposition, [status(thm), theory('equality')], [c_127, c_2413])).
% 8.77/3.07  tff(c_2660, plain, (![A_281]: (u1_struct_0(k2_tsep_1(A_281, '#skF_5', '#skF_6'))=k3_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_6', A_281) | ~m1_pre_topc('#skF_5', A_281) | ~l1_pre_topc(A_281) | v2_struct_0(A_281))), inference(negUnitSimplification, [status(thm)], [c_68, c_52, c_2629])).
% 8.77/3.07  tff(c_2849, plain, (![A_137]: (k3_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))=k2_struct_0(k2_tsep_1(A_137, '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_6', A_137) | ~m1_pre_topc('#skF_5', A_137) | ~l1_pre_topc(A_137) | v2_struct_0(A_137) | ~m1_pre_topc('#skF_6', A_137) | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', A_137) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_137) | v2_struct_0(A_137))), inference(superposition, [status(thm), theory('equality')], [c_508, c_2660])).
% 8.77/3.07  tff(c_2867, plain, (![A_137]: (k3_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))=k2_struct_0(k2_tsep_1(A_137, '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_6', A_137) | ~m1_pre_topc('#skF_5', A_137) | ~l1_pre_topc(A_137) | v2_struct_0(A_137) | ~m1_pre_topc('#skF_6', A_137) | ~m1_pre_topc('#skF_5', A_137) | ~l1_pre_topc(A_137) | v2_struct_0(A_137))), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_2849])).
% 8.77/3.07  tff(c_74, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.07  tff(c_72, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.07  tff(c_2655, plain, (![A_279]: (u1_struct_0(k2_tsep_1(A_279, '#skF_5', '#skF_6'))=k3_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_6', A_279) | ~m1_pre_topc('#skF_5', A_279) | ~l1_pre_topc(A_279) | v2_struct_0(A_279))), inference(negUnitSimplification, [status(thm)], [c_68, c_52, c_2629])).
% 8.77/3.07  tff(c_126, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_102, c_112])).
% 8.77/3.07  tff(c_163, plain, (![B_92, C_93, A_94]: (r1_tarski(u1_struct_0(B_92), u1_struct_0(C_93)) | ~m1_pre_topc(B_92, C_93) | ~m1_pre_topc(C_93, A_94) | ~m1_pre_topc(B_92, A_94) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.77/3.07  tff(c_167, plain, (![B_92]: (r1_tarski(u1_struct_0(B_92), u1_struct_0('#skF_7')) | ~m1_pre_topc(B_92, '#skF_7') | ~m1_pre_topc(B_92, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_163])).
% 8.77/3.07  tff(c_179, plain, (![B_92]: (r1_tarski(u1_struct_0(B_92), k2_struct_0('#skF_7')) | ~m1_pre_topc(B_92, '#skF_7') | ~m1_pre_topc(B_92, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_126, c_167])).
% 8.77/3.07  tff(c_2823, plain, (![A_281]: (r1_tarski(k3_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6')), k2_struct_0('#skF_7')) | ~m1_pre_topc(k2_tsep_1(A_281, '#skF_5', '#skF_6'), '#skF_7') | ~m1_pre_topc(k2_tsep_1(A_281, '#skF_5', '#skF_6'), '#skF_4') | ~m1_pre_topc('#skF_6', A_281) | ~m1_pre_topc('#skF_5', A_281) | ~l1_pre_topc(A_281) | v2_struct_0(A_281))), inference(superposition, [status(thm), theory('equality')], [c_2660, c_179])).
% 8.77/3.07  tff(c_4889, plain, (r1_tarski(k3_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6')), k2_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_2823])).
% 8.77/3.07  tff(c_4892, plain, (![A_298]: (r1_tarski(u1_struct_0(k2_tsep_1(A_298, '#skF_5', '#skF_6')), k2_struct_0('#skF_7')) | ~m1_pre_topc('#skF_6', A_298) | ~m1_pre_topc('#skF_5', A_298) | ~l1_pre_topc(A_298) | v2_struct_0(A_298))), inference(superposition, [status(thm), theory('equality')], [c_2655, c_4889])).
% 8.77/3.07  tff(c_146, plain, (![B_89, C_90, A_91]: (m1_pre_topc(B_89, C_90) | ~r1_tarski(u1_struct_0(B_89), u1_struct_0(C_90)) | ~m1_pre_topc(C_90, A_91) | ~m1_pre_topc(B_89, A_91) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.77/3.07  tff(c_158, plain, (![B_89, A_91]: (m1_pre_topc(B_89, '#skF_7') | ~r1_tarski(u1_struct_0(B_89), k2_struct_0('#skF_7')) | ~m1_pre_topc('#skF_7', A_91) | ~m1_pre_topc(B_89, A_91) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91))), inference(superposition, [status(thm), theory('equality')], [c_126, c_146])).
% 8.77/3.07  tff(c_4938, plain, (![A_303, A_304]: (m1_pre_topc(k2_tsep_1(A_303, '#skF_5', '#skF_6'), '#skF_7') | ~m1_pre_topc('#skF_7', A_304) | ~m1_pre_topc(k2_tsep_1(A_303, '#skF_5', '#skF_6'), A_304) | ~l1_pre_topc(A_304) | ~v2_pre_topc(A_304) | ~m1_pre_topc('#skF_6', A_303) | ~m1_pre_topc('#skF_5', A_303) | ~l1_pre_topc(A_303) | v2_struct_0(A_303))), inference(resolution, [status(thm)], [c_4892, c_158])).
% 8.77/3.07  tff(c_4941, plain, (![A_61]: (m1_pre_topc(k2_tsep_1(A_61, '#skF_5', '#skF_6'), '#skF_7') | ~m1_pre_topc('#skF_7', A_61) | ~v2_pre_topc(A_61) | ~m1_pre_topc('#skF_6', A_61) | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', A_61) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(resolution, [status(thm)], [c_40, c_4938])).
% 8.77/3.07  tff(c_4945, plain, (![A_305]: (m1_pre_topc(k2_tsep_1(A_305, '#skF_5', '#skF_6'), '#skF_7') | ~m1_pre_topc('#skF_7', A_305) | ~v2_pre_topc(A_305) | ~m1_pre_topc('#skF_6', A_305) | ~m1_pre_topc('#skF_5', A_305) | ~l1_pre_topc(A_305) | v2_struct_0(A_305))), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_4941])).
% 8.77/3.07  tff(c_50, plain, (~m1_pre_topc(k2_tsep_1('#skF_4', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.77/3.07  tff(c_4955, plain, (~m1_pre_topc('#skF_7', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_4945, c_50])).
% 8.77/3.07  tff(c_4967, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_62, c_72, c_58, c_4955])).
% 8.77/3.07  tff(c_4969, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_4967])).
% 8.77/3.07  tff(c_4971, plain, (~r1_tarski(k3_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_6')), k2_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_2823])).
% 8.77/3.07  tff(c_5095, plain, (![A_314]: (~r1_tarski(k2_struct_0(k2_tsep_1(A_314, '#skF_5', '#skF_6')), k2_struct_0('#skF_7')) | ~m1_pre_topc('#skF_6', A_314) | ~m1_pre_topc('#skF_5', A_314) | ~l1_pre_topc(A_314) | v2_struct_0(A_314) | ~m1_pre_topc('#skF_6', A_314) | ~m1_pre_topc('#skF_5', A_314) | ~l1_pre_topc(A_314) | v2_struct_0(A_314))), inference(superposition, [status(thm), theory('equality')], [c_2867, c_4971])).
% 8.77/3.07  tff(c_5105, plain, (![A_314]: (~m1_pre_topc('#skF_6', A_314) | ~m1_pre_topc('#skF_5', A_314) | ~l1_pre_topc(A_314) | v2_struct_0(A_314) | ~m1_pre_topc(k2_tsep_1(A_314, '#skF_5', '#skF_6'), '#skF_7') | ~l1_pre_topc(k2_tsep_1(A_314, '#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_7'))), inference(resolution, [status(thm)], [c_22, c_5095])).
% 8.77/3.07  tff(c_5111, plain, (![A_315]: (~m1_pre_topc('#skF_6', A_315) | ~m1_pre_topc('#skF_5', A_315) | ~l1_pre_topc(A_315) | v2_struct_0(A_315) | ~m1_pre_topc(k2_tsep_1(A_315, '#skF_5', '#skF_6'), '#skF_7') | ~l1_pre_topc(k2_tsep_1(A_315, '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_5105])).
% 8.77/3.07  tff(c_5115, plain, (~l1_pre_topc(k2_tsep_1('#skF_7', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_6', '#skF_7') | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_7') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_40, c_5111])).
% 8.77/3.07  tff(c_5118, plain, (~l1_pre_topc(k2_tsep_1('#skF_7', '#skF_5', '#skF_6')) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_56, c_54, c_5115])).
% 8.77/3.07  tff(c_5119, plain, (~l1_pre_topc(k2_tsep_1('#skF_7', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_68, c_64, c_5118])).
% 8.77/3.07  tff(c_5122, plain, (~m1_pre_topc('#skF_6', '#skF_7') | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_7') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_309, c_5119])).
% 8.77/3.07  tff(c_5125, plain, (v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_56, c_54, c_5122])).
% 8.77/3.07  tff(c_5127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_68, c_64, c_5125])).
% 8.77/3.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.77/3.07  
% 8.77/3.07  Inference rules
% 8.77/3.07  ----------------------
% 8.77/3.07  #Ref     : 0
% 8.77/3.07  #Sup     : 1603
% 8.77/3.07  #Fact    : 0
% 8.77/3.07  #Define  : 0
% 8.77/3.07  #Split   : 36
% 8.77/3.07  #Chain   : 0
% 8.77/3.07  #Close   : 0
% 8.77/3.07  
% 8.77/3.07  Ordering : KBO
% 8.77/3.07  
% 8.77/3.07  Simplification rules
% 8.77/3.07  ----------------------
% 8.77/3.07  #Subsume      : 107
% 8.77/3.07  #Demod        : 499
% 8.77/3.07  #Tautology    : 189
% 8.77/3.07  #SimpNegUnit  : 280
% 8.77/3.07  #BackRed      : 0
% 8.77/3.07  
% 8.77/3.07  #Partial instantiations: 0
% 8.77/3.07  #Strategies tried      : 1
% 8.77/3.07  
% 8.77/3.07  Timing (in seconds)
% 8.77/3.07  ----------------------
% 8.77/3.07  Preprocessing        : 0.35
% 8.77/3.07  Parsing              : 0.18
% 8.77/3.07  CNF conversion       : 0.03
% 8.77/3.07  Main loop            : 1.95
% 8.77/3.07  Inferencing          : 0.47
% 8.77/3.07  Reduction            : 0.59
% 8.77/3.08  Demodulation         : 0.41
% 8.77/3.08  BG Simplification    : 0.09
% 8.77/3.08  Subsumption          : 0.71
% 8.77/3.08  Abstraction          : 0.09
% 8.77/3.08  MUC search           : 0.00
% 8.77/3.08  Cooper               : 0.00
% 8.77/3.08  Total                : 2.34
% 8.77/3.08  Index Insertion      : 0.00
% 8.77/3.08  Index Deletion       : 0.00
% 8.77/3.08  Index Matching       : 0.00
% 8.77/3.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
