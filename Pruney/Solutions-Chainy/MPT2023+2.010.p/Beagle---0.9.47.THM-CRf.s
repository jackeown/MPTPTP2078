%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:13 EST 2020

% Result     : Theorem 9.61s
% Output     : CNFRefutation 9.84s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 435 expanded)
%              Number of leaves         :   32 ( 183 expanded)
%              Depth                    :   17
%              Number of atoms          :  220 (1688 expanded)
%              Number of equality atoms :    9 (  68 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_131,negated_conjecture,(
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

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & D = C
                  & r2_hidden(B,D)
                  & v3_pre_topc(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).

tff(f_112,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_62,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_60,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_56,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_414,plain,(
    ! [A_134,B_135,C_136] :
      ( '#skF_4'(A_134,B_135,C_136) = C_136
      | ~ m1_subset_1(C_136,u1_struct_0(k9_yellow_6(A_134,B_135)))
      | ~ m1_subset_1(B_135,u1_struct_0(A_134))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_440,plain,
    ( '#skF_4'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_414])).

tff(c_452,plain,
    ( '#skF_4'('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_440])).

tff(c_453,plain,(
    '#skF_4'('#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_452])).

tff(c_733,plain,(
    ! [B_176,A_177,C_178] :
      ( r2_hidden(B_176,'#skF_4'(A_177,B_176,C_178))
      | ~ m1_subset_1(C_178,u1_struct_0(k9_yellow_6(A_177,B_176)))
      | ~ m1_subset_1(B_176,u1_struct_0(A_177))
      | ~ l1_pre_topc(A_177)
      | ~ v2_pre_topc(A_177)
      | v2_struct_0(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_761,plain,
    ( r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_733])).

tff(c_776,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_453,c_761])).

tff(c_777,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_776])).

tff(c_54,plain,(
    m1_subset_1('#skF_8',u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_437,plain,
    ( '#skF_4'('#skF_5','#skF_6','#skF_8') = '#skF_8'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_414])).

tff(c_448,plain,
    ( '#skF_4'('#skF_5','#skF_6','#skF_8') = '#skF_8'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_437])).

tff(c_449,plain,(
    '#skF_4'('#skF_5','#skF_6','#skF_8') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_448])).

tff(c_759,plain,
    ( r2_hidden('#skF_6','#skF_4'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_733])).

tff(c_772,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_449,c_759])).

tff(c_773,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_772])).

tff(c_8,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,k3_xboole_0(A_6,B_7))
      | ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1504,plain,(
    ! [A_273,B_274,C_275] :
      ( m1_subset_1('#skF_4'(A_273,B_274,C_275),k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ m1_subset_1(C_275,u1_struct_0(k9_yellow_6(A_273,B_274)))
      | ~ m1_subset_1(B_274,u1_struct_0(A_273))
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1515,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_8',u1_struct_0(k9_yellow_6('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_1504])).

tff(c_1522,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_54,c_1515])).

tff(c_1523,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1522])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1576,plain,(
    r1_tarski('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1523,c_30])).

tff(c_83,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_1'(A_70,B_71),A_70)
      | r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_230,plain,(
    ! [A_103,B_104,B_105] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_103,B_104),B_105),B_104)
      | r1_tarski(k3_xboole_0(A_103,B_104),B_105) ) ),
    inference(resolution,[status(thm)],[c_83,c_10])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2381,plain,(
    ! [A_326,B_327,B_328,B_329] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_326,B_327),B_328),B_329)
      | ~ r1_tarski(B_327,B_329)
      | r1_tarski(k3_xboole_0(A_326,B_327),B_328) ) ),
    inference(resolution,[status(thm)],[c_230,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2421,plain,(
    ! [B_327,B_329,A_326] :
      ( ~ r1_tarski(B_327,B_329)
      | r1_tarski(k3_xboole_0(A_326,B_327),B_329) ) ),
    inference(resolution,[status(thm)],[c_2381,c_4])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_864,plain,(
    ! [A_183,B_184,C_185] :
      ( v3_pre_topc('#skF_4'(A_183,B_184,C_185),A_183)
      | ~ m1_subset_1(C_185,u1_struct_0(k9_yellow_6(A_183,B_184)))
      | ~ m1_subset_1(B_184,u1_struct_0(A_183))
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_892,plain,
    ( v3_pre_topc('#skF_4'('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_864])).

tff(c_907,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_453,c_892])).

tff(c_908,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_907])).

tff(c_1512,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_1504])).

tff(c_1519,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_1512])).

tff(c_1520,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1519])).

tff(c_890,plain,
    ( v3_pre_topc('#skF_4'('#skF_5','#skF_6','#skF_8'),'#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_864])).

tff(c_903,plain,
    ( v3_pre_topc('#skF_8','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_449,c_890])).

tff(c_904,plain,(
    v3_pre_topc('#skF_8','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_903])).

tff(c_1616,plain,(
    ! [B_279,C_280,A_281] :
      ( v3_pre_topc(k3_xboole_0(B_279,C_280),A_281)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ v3_pre_topc(C_280,A_281)
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ v3_pre_topc(B_279,A_281)
      | ~ l1_pre_topc(A_281)
      | ~ v2_pre_topc(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1618,plain,(
    ! [B_279] :
      ( v3_pre_topc(k3_xboole_0(B_279,'#skF_8'),'#skF_5')
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_279,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1523,c_1616])).

tff(c_1863,plain,(
    ! [B_305] :
      ( v3_pre_topc(k3_xboole_0(B_305,'#skF_8'),'#skF_5')
      | ~ m1_subset_1(B_305,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_305,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_904,c_1618])).

tff(c_1869,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_7','#skF_8'),'#skF_5')
    | ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_1520,c_1863])).

tff(c_1915,plain,(
    v3_pre_topc(k3_xboole_0('#skF_7','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_1869])).

tff(c_1821,plain,(
    ! [C_300,A_301,B_302] :
      ( r2_hidden(C_300,u1_struct_0(k9_yellow_6(A_301,B_302)))
      | ~ v3_pre_topc(C_300,A_301)
      | ~ r2_hidden(B_302,C_300)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ m1_subset_1(B_302,u1_struct_0(A_301))
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_11765,plain,(
    ! [C_730,A_731,B_732] :
      ( m1_subset_1(C_730,u1_struct_0(k9_yellow_6(A_731,B_732)))
      | ~ v3_pre_topc(C_730,A_731)
      | ~ r2_hidden(B_732,C_730)
      | ~ m1_subset_1(C_730,k1_zfmisc_1(u1_struct_0(A_731)))
      | ~ m1_subset_1(B_732,u1_struct_0(A_731))
      | ~ l1_pre_topc(A_731)
      | ~ v2_pre_topc(A_731)
      | v2_struct_0(A_731) ) ),
    inference(resolution,[status(thm)],[c_1821,c_28])).

tff(c_52,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_7','#skF_8'),u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_11778,plain,
    ( ~ v3_pre_topc(k3_xboole_0('#skF_7','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_6',k3_xboole_0('#skF_7','#skF_8'))
    | ~ m1_subset_1(k3_xboole_0('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_11765,c_52])).

tff(c_11785,plain,
    ( ~ r2_hidden('#skF_6',k3_xboole_0('#skF_7','#skF_8'))
    | ~ m1_subset_1(k3_xboole_0('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_1915,c_11778])).

tff(c_11786,plain,
    ( ~ r2_hidden('#skF_6',k3_xboole_0('#skF_7','#skF_8'))
    | ~ m1_subset_1(k3_xboole_0('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11785])).

tff(c_11787,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_11786])).

tff(c_11791,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_7','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_32,c_11787])).

tff(c_11794,plain,(
    ~ r1_tarski('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2421,c_11791])).

tff(c_11807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1576,c_11794])).

tff(c_11808,plain,(
    ~ r2_hidden('#skF_6',k3_xboole_0('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_11786])).

tff(c_11827,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_8,c_11808])).

tff(c_11838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_773,c_11827])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.61/3.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.80/3.47  
% 9.80/3.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.80/3.47  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1
% 9.80/3.47  
% 9.80/3.47  %Foreground sorts:
% 9.80/3.47  
% 9.80/3.47  
% 9.80/3.47  %Background operators:
% 9.80/3.47  
% 9.80/3.47  
% 9.80/3.47  %Foreground operators:
% 9.80/3.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.80/3.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.80/3.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.80/3.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.80/3.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.80/3.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.80/3.47  tff('#skF_7', type, '#skF_7': $i).
% 9.80/3.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.80/3.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.80/3.47  tff('#skF_5', type, '#skF_5': $i).
% 9.80/3.47  tff('#skF_6', type, '#skF_6': $i).
% 9.80/3.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.80/3.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.80/3.47  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 9.80/3.47  tff('#skF_8', type, '#skF_8': $i).
% 9.80/3.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.80/3.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.80/3.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.80/3.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.80/3.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.80/3.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.80/3.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.80/3.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.80/3.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.80/3.47  
% 9.84/3.49  tff(f_131, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k3_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_waybel_9)).
% 9.84/3.49  tff(f_93, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & (D = C)) & r2_hidden(B, D)) & v3_pre_topc(D, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_yellow_6)).
% 9.84/3.49  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 9.84/3.49  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.84/3.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.84/3.49  tff(f_71, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_tops_1)).
% 9.84/3.49  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 9.84/3.49  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 9.84/3.49  tff(c_64, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.84/3.49  tff(c_62, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.84/3.49  tff(c_60, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.84/3.49  tff(c_58, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.84/3.49  tff(c_56, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.84/3.49  tff(c_414, plain, (![A_134, B_135, C_136]: ('#skF_4'(A_134, B_135, C_136)=C_136 | ~m1_subset_1(C_136, u1_struct_0(k9_yellow_6(A_134, B_135))) | ~m1_subset_1(B_135, u1_struct_0(A_134)) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.84/3.49  tff(c_440, plain, ('#skF_4'('#skF_5', '#skF_6', '#skF_7')='#skF_7' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_414])).
% 9.84/3.49  tff(c_452, plain, ('#skF_4'('#skF_5', '#skF_6', '#skF_7')='#skF_7' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_440])).
% 9.84/3.49  tff(c_453, plain, ('#skF_4'('#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_64, c_452])).
% 9.84/3.49  tff(c_733, plain, (![B_176, A_177, C_178]: (r2_hidden(B_176, '#skF_4'(A_177, B_176, C_178)) | ~m1_subset_1(C_178, u1_struct_0(k9_yellow_6(A_177, B_176))) | ~m1_subset_1(B_176, u1_struct_0(A_177)) | ~l1_pre_topc(A_177) | ~v2_pre_topc(A_177) | v2_struct_0(A_177))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.84/3.49  tff(c_761, plain, (r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_733])).
% 9.84/3.49  tff(c_776, plain, (r2_hidden('#skF_6', '#skF_7') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_453, c_761])).
% 9.84/3.49  tff(c_777, plain, (r2_hidden('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_64, c_776])).
% 9.84/3.49  tff(c_54, plain, (m1_subset_1('#skF_8', u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.84/3.49  tff(c_437, plain, ('#skF_4'('#skF_5', '#skF_6', '#skF_8')='#skF_8' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_414])).
% 9.84/3.49  tff(c_448, plain, ('#skF_4'('#skF_5', '#skF_6', '#skF_8')='#skF_8' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_437])).
% 9.84/3.49  tff(c_449, plain, ('#skF_4'('#skF_5', '#skF_6', '#skF_8')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_64, c_448])).
% 9.84/3.49  tff(c_759, plain, (r2_hidden('#skF_6', '#skF_4'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_733])).
% 9.84/3.49  tff(c_772, plain, (r2_hidden('#skF_6', '#skF_8') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_449, c_759])).
% 9.84/3.49  tff(c_773, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_64, c_772])).
% 9.84/3.49  tff(c_8, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, k3_xboole_0(A_6, B_7)) | ~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.84/3.49  tff(c_1504, plain, (![A_273, B_274, C_275]: (m1_subset_1('#skF_4'(A_273, B_274, C_275), k1_zfmisc_1(u1_struct_0(A_273))) | ~m1_subset_1(C_275, u1_struct_0(k9_yellow_6(A_273, B_274))) | ~m1_subset_1(B_274, u1_struct_0(A_273)) | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.84/3.49  tff(c_1515, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', u1_struct_0(k9_yellow_6('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_449, c_1504])).
% 9.84/3.49  tff(c_1522, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_54, c_1515])).
% 9.84/3.49  tff(c_1523, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_1522])).
% 9.84/3.49  tff(c_30, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.84/3.49  tff(c_1576, plain, (r1_tarski('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1523, c_30])).
% 9.84/3.49  tff(c_83, plain, (![A_70, B_71]: (r2_hidden('#skF_1'(A_70, B_71), A_70) | r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.84/3.49  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.84/3.49  tff(c_230, plain, (![A_103, B_104, B_105]: (r2_hidden('#skF_1'(k3_xboole_0(A_103, B_104), B_105), B_104) | r1_tarski(k3_xboole_0(A_103, B_104), B_105))), inference(resolution, [status(thm)], [c_83, c_10])).
% 9.84/3.49  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.84/3.49  tff(c_2381, plain, (![A_326, B_327, B_328, B_329]: (r2_hidden('#skF_1'(k3_xboole_0(A_326, B_327), B_328), B_329) | ~r1_tarski(B_327, B_329) | r1_tarski(k3_xboole_0(A_326, B_327), B_328))), inference(resolution, [status(thm)], [c_230, c_2])).
% 9.84/3.49  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.84/3.49  tff(c_2421, plain, (![B_327, B_329, A_326]: (~r1_tarski(B_327, B_329) | r1_tarski(k3_xboole_0(A_326, B_327), B_329))), inference(resolution, [status(thm)], [c_2381, c_4])).
% 9.84/3.49  tff(c_32, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.84/3.49  tff(c_864, plain, (![A_183, B_184, C_185]: (v3_pre_topc('#skF_4'(A_183, B_184, C_185), A_183) | ~m1_subset_1(C_185, u1_struct_0(k9_yellow_6(A_183, B_184))) | ~m1_subset_1(B_184, u1_struct_0(A_183)) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.84/3.49  tff(c_892, plain, (v3_pre_topc('#skF_4'('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_864])).
% 9.84/3.49  tff(c_907, plain, (v3_pre_topc('#skF_7', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_453, c_892])).
% 9.84/3.49  tff(c_908, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_907])).
% 9.84/3.49  tff(c_1512, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_453, c_1504])).
% 9.84/3.49  tff(c_1519, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_1512])).
% 9.84/3.49  tff(c_1520, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_1519])).
% 9.84/3.49  tff(c_890, plain, (v3_pre_topc('#skF_4'('#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_864])).
% 9.84/3.49  tff(c_903, plain, (v3_pre_topc('#skF_8', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_449, c_890])).
% 9.84/3.49  tff(c_904, plain, (v3_pre_topc('#skF_8', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_903])).
% 9.84/3.49  tff(c_1616, plain, (![B_279, C_280, A_281]: (v3_pre_topc(k3_xboole_0(B_279, C_280), A_281) | ~m1_subset_1(C_280, k1_zfmisc_1(u1_struct_0(A_281))) | ~v3_pre_topc(C_280, A_281) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_281))) | ~v3_pre_topc(B_279, A_281) | ~l1_pre_topc(A_281) | ~v2_pre_topc(A_281))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.84/3.49  tff(c_1618, plain, (![B_279]: (v3_pre_topc(k3_xboole_0(B_279, '#skF_8'), '#skF_5') | ~v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_279, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_1523, c_1616])).
% 9.84/3.49  tff(c_1863, plain, (![B_305]: (v3_pre_topc(k3_xboole_0(B_305, '#skF_8'), '#skF_5') | ~m1_subset_1(B_305, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_305, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_904, c_1618])).
% 9.84/3.49  tff(c_1869, plain, (v3_pre_topc(k3_xboole_0('#skF_7', '#skF_8'), '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_1520, c_1863])).
% 9.84/3.49  tff(c_1915, plain, (v3_pre_topc(k3_xboole_0('#skF_7', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_908, c_1869])).
% 9.84/3.49  tff(c_1821, plain, (![C_300, A_301, B_302]: (r2_hidden(C_300, u1_struct_0(k9_yellow_6(A_301, B_302))) | ~v3_pre_topc(C_300, A_301) | ~r2_hidden(B_302, C_300) | ~m1_subset_1(C_300, k1_zfmisc_1(u1_struct_0(A_301))) | ~m1_subset_1(B_302, u1_struct_0(A_301)) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.84/3.49  tff(c_28, plain, (![A_14, B_15]: (m1_subset_1(A_14, B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.84/3.49  tff(c_11765, plain, (![C_730, A_731, B_732]: (m1_subset_1(C_730, u1_struct_0(k9_yellow_6(A_731, B_732))) | ~v3_pre_topc(C_730, A_731) | ~r2_hidden(B_732, C_730) | ~m1_subset_1(C_730, k1_zfmisc_1(u1_struct_0(A_731))) | ~m1_subset_1(B_732, u1_struct_0(A_731)) | ~l1_pre_topc(A_731) | ~v2_pre_topc(A_731) | v2_struct_0(A_731))), inference(resolution, [status(thm)], [c_1821, c_28])).
% 9.84/3.49  tff(c_52, plain, (~m1_subset_1(k3_xboole_0('#skF_7', '#skF_8'), u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.84/3.49  tff(c_11778, plain, (~v3_pre_topc(k3_xboole_0('#skF_7', '#skF_8'), '#skF_5') | ~r2_hidden('#skF_6', k3_xboole_0('#skF_7', '#skF_8')) | ~m1_subset_1(k3_xboole_0('#skF_7', '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_11765, c_52])).
% 9.84/3.49  tff(c_11785, plain, (~r2_hidden('#skF_6', k3_xboole_0('#skF_7', '#skF_8')) | ~m1_subset_1(k3_xboole_0('#skF_7', '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_1915, c_11778])).
% 9.84/3.49  tff(c_11786, plain, (~r2_hidden('#skF_6', k3_xboole_0('#skF_7', '#skF_8')) | ~m1_subset_1(k3_xboole_0('#skF_7', '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_11785])).
% 9.84/3.49  tff(c_11787, plain, (~m1_subset_1(k3_xboole_0('#skF_7', '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_11786])).
% 9.84/3.49  tff(c_11791, plain, (~r1_tarski(k3_xboole_0('#skF_7', '#skF_8'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_11787])).
% 9.84/3.49  tff(c_11794, plain, (~r1_tarski('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_2421, c_11791])).
% 9.84/3.49  tff(c_11807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1576, c_11794])).
% 9.84/3.49  tff(c_11808, plain, (~r2_hidden('#skF_6', k3_xboole_0('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_11786])).
% 9.84/3.49  tff(c_11827, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_8, c_11808])).
% 9.84/3.49  tff(c_11838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_777, c_773, c_11827])).
% 9.84/3.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.84/3.49  
% 9.84/3.49  Inference rules
% 9.84/3.49  ----------------------
% 9.84/3.49  #Ref     : 0
% 9.84/3.49  #Sup     : 2835
% 9.84/3.49  #Fact    : 0
% 9.84/3.49  #Define  : 0
% 9.84/3.49  #Split   : 3
% 9.84/3.49  #Chain   : 0
% 9.84/3.49  #Close   : 0
% 9.84/3.49  
% 9.84/3.49  Ordering : KBO
% 9.84/3.49  
% 9.84/3.49  Simplification rules
% 9.84/3.49  ----------------------
% 9.84/3.49  #Subsume      : 710
% 9.84/3.49  #Demod        : 722
% 9.84/3.49  #Tautology    : 359
% 9.84/3.49  #SimpNegUnit  : 17
% 9.84/3.49  #BackRed      : 1
% 9.84/3.49  
% 9.84/3.49  #Partial instantiations: 0
% 9.84/3.49  #Strategies tried      : 1
% 9.84/3.49  
% 9.84/3.49  Timing (in seconds)
% 9.84/3.49  ----------------------
% 9.84/3.49  Preprocessing        : 0.32
% 9.84/3.49  Parsing              : 0.17
% 9.84/3.49  CNF conversion       : 0.03
% 9.84/3.49  Main loop            : 2.39
% 9.84/3.49  Inferencing          : 0.66
% 9.84/3.49  Reduction            : 0.61
% 9.84/3.49  Demodulation         : 0.43
% 9.84/3.49  BG Simplification    : 0.07
% 9.84/3.49  Subsumption          : 0.86
% 9.84/3.49  Abstraction          : 0.10
% 9.84/3.49  MUC search           : 0.00
% 9.84/3.49  Cooper               : 0.00
% 9.84/3.49  Total                : 2.74
% 9.84/3.49  Index Insertion      : 0.00
% 9.84/3.49  Index Deletion       : 0.00
% 9.84/3.49  Index Matching       : 0.00
% 9.84/3.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
