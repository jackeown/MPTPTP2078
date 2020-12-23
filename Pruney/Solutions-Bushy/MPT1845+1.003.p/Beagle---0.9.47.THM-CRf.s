%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1845+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:32 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :  177 (7537 expanded)
%              Number of leaves         :   28 (2440 expanded)
%              Depth                    :   22
%              Number of atoms          :  412 (20996 expanded)
%              Number of equality atoms :   44 (7420 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k3_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v2_pre_topc(A) )
             => v2_pre_topc(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tex_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(c_50,plain,(
    ~ v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_56,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,(
    ! [A_17] :
      ( m1_subset_1(u1_pre_topc(A_17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17))))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_120,plain,(
    ! [C_40,A_41,D_42,B_43] :
      ( C_40 = A_41
      | g1_pre_topc(C_40,D_42) != g1_pre_topc(A_41,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_143,plain,(
    ! [A_50,B_51] :
      ( u1_struct_0('#skF_5') = A_50
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(A_50,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_50))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_120])).

tff(c_147,plain,(
    ! [A_17] :
      ( u1_struct_0(A_17) = u1_struct_0('#skF_5')
      | g1_pre_topc(u1_struct_0(A_17),u1_pre_topc(A_17)) != g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_40,c_143])).

tff(c_160,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_147])).

tff(c_162,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_160])).

tff(c_189,plain,
    ( m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_40])).

tff(c_202,plain,(
    m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_189])).

tff(c_129,plain,(
    ! [D_44,B_45,C_46,A_47] :
      ( D_44 = B_45
      | g1_pre_topc(C_46,D_44) != g1_pre_topc(A_47,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k1_zfmisc_1(A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_133,plain,(
    ! [D_44,C_46] :
      ( u1_pre_topc('#skF_5') = D_44
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_46,D_44)
      | ~ m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_129])).

tff(c_1506,plain,(
    ! [D_44,C_46] :
      ( u1_pre_topc('#skF_5') = D_44
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_46,D_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_162,c_133])).

tff(c_1509,plain,(
    u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1506])).

tff(c_347,plain,(
    ! [D_44,C_46] :
      ( u1_pre_topc('#skF_5') = D_44
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_46,D_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_162,c_133])).

tff(c_350,plain,(
    u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_347])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_38,plain,(
    ! [A_3] :
      ( r2_hidden(u1_struct_0(A_3),u1_pre_topc(A_3))
      | ~ v2_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_153,plain,(
    ! [B_53,A_54] :
      ( u1_pre_topc('#skF_5') = B_53
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(A_54,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_129])).

tff(c_157,plain,(
    ! [A_17] :
      ( u1_pre_topc(A_17) = u1_pre_topc('#skF_5')
      | g1_pre_topc(u1_struct_0(A_17),u1_pre_topc(A_17)) != g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_40,c_153])).

tff(c_270,plain,
    ( u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_157])).

tff(c_272,plain,(
    u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_270])).

tff(c_18,plain,(
    ! [A_3] :
      ( r1_tarski('#skF_1'(A_3),u1_pre_topc(A_3))
      | r2_hidden('#skF_2'(A_3),u1_pre_topc(A_3))
      | v2_pre_topc(A_3)
      | ~ r2_hidden(u1_struct_0(A_3),u1_pre_topc(A_3))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_177,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_18])).

tff(c_193,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_177])).

tff(c_194,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_193])).

tff(c_256,plain,(
    ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_281,plain,(
    ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_256])).

tff(c_325,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_281])).

tff(c_329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_325])).

tff(c_331,plain,(
    r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_359,plain,(
    r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_331])).

tff(c_561,plain,(
    ! [A_75] :
      ( m1_subset_1('#skF_1'(A_75),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_75))))
      | m1_subset_1('#skF_3'(A_75),k1_zfmisc_1(u1_struct_0(A_75)))
      | v2_pre_topc(A_75)
      | ~ r2_hidden(u1_struct_0(A_75),u1_pre_topc(A_75))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_569,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_561])).

tff(c_573,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_359,c_350,c_162,c_162,c_569])).

tff(c_574,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_573])).

tff(c_575,plain,(
    m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_574])).

tff(c_481,plain,(
    ! [A_68] :
      ( m1_subset_1('#skF_1'(A_68),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_68))))
      | r2_hidden('#skF_3'(A_68),u1_pre_topc(A_68))
      | v2_pre_topc(A_68)
      | ~ r2_hidden(u1_struct_0(A_68),u1_pre_topc(A_68))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_489,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_481])).

tff(c_493,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_359,c_350,c_162,c_350,c_489])).

tff(c_494,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_493])).

tff(c_495,plain,(
    r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_494])).

tff(c_588,plain,(
    ! [A_77] :
      ( m1_subset_1('#skF_1'(A_77),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_77))))
      | m1_subset_1('#skF_2'(A_77),k1_zfmisc_1(u1_struct_0(A_77)))
      | v2_pre_topc(A_77)
      | ~ r2_hidden(u1_struct_0(A_77),u1_pre_topc(A_77))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_596,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_588])).

tff(c_600,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_359,c_350,c_162,c_162,c_596])).

tff(c_601,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_600])).

tff(c_620,plain,(
    m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_601])).

tff(c_528,plain,(
    ! [A_73] :
      ( m1_subset_1('#skF_1'(A_73),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_73))))
      | r2_hidden('#skF_2'(A_73),u1_pre_topc(A_73))
      | v2_pre_topc(A_73)
      | ~ r2_hidden(u1_struct_0(A_73),u1_pre_topc(A_73))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_536,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_528])).

tff(c_540,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_359,c_350,c_162,c_350,c_536])).

tff(c_541,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_540])).

tff(c_542,plain,(
    r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_541])).

tff(c_48,plain,(
    ! [A_26,B_27,C_28] :
      ( k9_subset_1(A_26,B_27,C_28) = k3_xboole_0(B_27,C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_623,plain,(
    ! [B_27] : k9_subset_1(u1_struct_0('#skF_4'),B_27,'#skF_2'('#skF_5')) = k3_xboole_0(B_27,'#skF_2'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_620,c_48])).

tff(c_971,plain,(
    ! [A_103,B_104,C_105] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_103),B_104,C_105),u1_pre_topc(A_103))
      | ~ r2_hidden(C_105,u1_pre_topc(A_103))
      | ~ r2_hidden(B_104,u1_pre_topc(A_103))
      | ~ m1_subset_1(C_105,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ v2_pre_topc(A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_986,plain,(
    ! [B_27] :
      ( r2_hidden(k3_xboole_0(B_27,'#skF_2'('#skF_5')),u1_pre_topc('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
      | ~ r2_hidden(B_27,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_971])).

tff(c_1007,plain,(
    ! [B_106] :
      ( r2_hidden(k3_xboole_0(B_106,'#skF_2'('#skF_5')),u1_pre_topc('#skF_4'))
      | ~ r2_hidden(B_106,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_620,c_542,c_986])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_578,plain,(
    ! [B_27] : k9_subset_1(u1_struct_0('#skF_4'),B_27,'#skF_3'('#skF_5')) = k3_xboole_0(B_27,'#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_575,c_48])).

tff(c_807,plain,(
    ! [A_92] :
      ( m1_subset_1('#skF_1'(A_92),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_92))))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(A_92),'#skF_2'(A_92),'#skF_3'(A_92)),u1_pre_topc(A_92))
      | v2_pre_topc(A_92)
      | ~ r2_hidden(u1_struct_0(A_92),u1_pre_topc(A_92))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_810,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_5'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_807])).

tff(c_815,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ r2_hidden(k3_xboole_0('#skF_3'('#skF_5'),'#skF_2'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_359,c_350,c_162,c_2,c_578,c_162,c_162,c_810])).

tff(c_816,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ r2_hidden(k3_xboole_0('#skF_3'('#skF_5'),'#skF_2'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_815])).

tff(c_831,plain,(
    ~ r2_hidden(k3_xboole_0('#skF_3'('#skF_5'),'#skF_2'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_816])).

tff(c_1010,plain,
    ( ~ r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_1007,c_831])).

tff(c_1022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_495,c_1010])).

tff(c_1024,plain,(
    r2_hidden(k3_xboole_0('#skF_3'('#skF_5'),'#skF_2'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_816])).

tff(c_1023,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_816])).

tff(c_330,plain,
    ( r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_332,plain,(
    r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_358,plain,(
    r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_332])).

tff(c_46,plain,(
    ! [A_24,B_25] :
      ( k5_setfam_1(A_24,B_25) = k3_tarski(B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1031,plain,(
    k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k3_tarski('#skF_1'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1023,c_46])).

tff(c_36,plain,(
    ! [A_3,B_12] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_3),B_12),u1_pre_topc(A_3))
      | ~ r1_tarski(B_12,u1_pre_topc(A_3))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_3))))
      | ~ v2_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1035,plain,
    ( r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1031,c_36])).

tff(c_1039,plain,(
    r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_1023,c_358,c_1035])).

tff(c_1041,plain,(
    ! [A_107] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_107),'#skF_1'(A_107)),u1_pre_topc(A_107))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(A_107),'#skF_2'(A_107),'#skF_3'(A_107)),u1_pre_topc(A_107))
      | v2_pre_topc(A_107)
      | ~ r2_hidden(u1_struct_0(A_107),u1_pre_topc(A_107))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1044,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_5'))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_5'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_1041])).

tff(c_1049,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_359,c_162,c_350,c_1024,c_2,c_578,c_162,c_1039,c_1031,c_162,c_350,c_1044])).

tff(c_1051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1049])).

tff(c_1053,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_601])).

tff(c_1052,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_601])).

tff(c_1060,plain,(
    k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k3_tarski('#skF_1'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1052,c_46])).

tff(c_1064,plain,
    ( r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1060,c_36])).

tff(c_1068,plain,(
    r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_1052,c_358,c_1064])).

tff(c_1125,plain,(
    ! [A_111] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_111),'#skF_1'(A_111)),u1_pre_topc(A_111))
      | m1_subset_1('#skF_2'(A_111),k1_zfmisc_1(u1_struct_0(A_111)))
      | v2_pre_topc(A_111)
      | ~ r2_hidden(u1_struct_0(A_111),u1_pre_topc(A_111))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1132,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_1125])).

tff(c_1138,plain,
    ( m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_359,c_162,c_350,c_162,c_1068,c_1060,c_162,c_1132])).

tff(c_1140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1053,c_1138])).

tff(c_1142,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_1141,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_1163,plain,(
    k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k3_tarski('#skF_1'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1141,c_46])).

tff(c_1167,plain,
    ( r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1163,c_36])).

tff(c_1171,plain,(
    r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_1141,c_358,c_1167])).

tff(c_1265,plain,(
    ! [A_118] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_118),'#skF_1'(A_118)),u1_pre_topc(A_118))
      | m1_subset_1('#skF_3'(A_118),k1_zfmisc_1(u1_struct_0(A_118)))
      | v2_pre_topc(A_118)
      | ~ r2_hidden(u1_struct_0(A_118),u1_pre_topc(A_118))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1272,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_1265])).

tff(c_1278,plain,
    ( m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_359,c_162,c_350,c_162,c_1171,c_1163,c_162,c_1272])).

tff(c_1280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1142,c_1278])).

tff(c_1282,plain,(
    ~ r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_1281,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_1289,plain,(
    k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k3_tarski('#skF_1'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1281,c_46])).

tff(c_1293,plain,
    ( r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1289,c_36])).

tff(c_1297,plain,(
    r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_1281,c_358,c_1293])).

tff(c_1354,plain,(
    ! [A_123] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_123),'#skF_1'(A_123)),u1_pre_topc(A_123))
      | r2_hidden('#skF_2'(A_123),u1_pre_topc(A_123))
      | v2_pre_topc(A_123)
      | ~ r2_hidden(u1_struct_0(A_123),u1_pre_topc(A_123))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1361,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_1354])).

tff(c_1367,plain,
    ( r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_359,c_162,c_350,c_350,c_1297,c_1289,c_162,c_1361])).

tff(c_1369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1282,c_1367])).

tff(c_1371,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_494])).

tff(c_1370,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_494])).

tff(c_1397,plain,(
    k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k3_tarski('#skF_1'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1370,c_46])).

tff(c_1401,plain,
    ( r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1397,c_36])).

tff(c_1405,plain,(
    r2_hidden(k3_tarski('#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_1370,c_358,c_1401])).

tff(c_1462,plain,(
    ! [A_131] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_131),'#skF_1'(A_131)),u1_pre_topc(A_131))
      | r2_hidden('#skF_3'(A_131),u1_pre_topc(A_131))
      | v2_pre_topc(A_131)
      | ~ r2_hidden(u1_struct_0(A_131),u1_pre_topc(A_131))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1469,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_1462])).

tff(c_1475,plain,
    ( r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_359,c_162,c_350,c_350,c_1405,c_1397,c_162,c_1469])).

tff(c_1477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1371,c_1475])).

tff(c_1479,plain,(
    ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_1518,plain,(
    ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_1479])).

tff(c_1520,plain,(
    r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_331])).

tff(c_1573,plain,(
    ! [A_136] :
      ( r1_tarski('#skF_1'(A_136),u1_pre_topc(A_136))
      | m1_subset_1('#skF_3'(A_136),k1_zfmisc_1(u1_struct_0(A_136)))
      | v2_pre_topc(A_136)
      | ~ r2_hidden(u1_struct_0(A_136),u1_pre_topc(A_136))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1578,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_1573])).

tff(c_1581,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1520,c_1509,c_162,c_1509,c_1578])).

tff(c_1582,plain,(
    m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1518,c_1581])).

tff(c_245,plain,(
    ! [A_57] :
      ( r1_tarski('#skF_1'(A_57),u1_pre_topc(A_57))
      | r2_hidden('#skF_3'(A_57),u1_pre_topc(A_57))
      | v2_pre_topc(A_57)
      | ~ r2_hidden(u1_struct_0(A_57),u1_pre_topc(A_57))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_248,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_245])).

tff(c_253,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_248])).

tff(c_254,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_253])).

tff(c_1503,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_254])).

tff(c_1504,plain,(
    r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1479,c_1503])).

tff(c_1517,plain,(
    r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_1504])).

tff(c_1480,plain,(
    ! [A_132] :
      ( r1_tarski('#skF_1'(A_132),u1_pre_topc(A_132))
      | m1_subset_1('#skF_2'(A_132),k1_zfmisc_1(u1_struct_0(A_132)))
      | v2_pre_topc(A_132)
      | ~ r2_hidden(u1_struct_0(A_132),u1_pre_topc(A_132))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1485,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_1480])).

tff(c_1488,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_331,c_162,c_1485])).

tff(c_1489,plain,(
    m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1479,c_1488])).

tff(c_1478,plain,(
    r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_1519,plain,(
    r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_1478])).

tff(c_1492,plain,(
    ! [B_27] : k9_subset_1(u1_struct_0('#skF_4'),B_27,'#skF_2'('#skF_5')) = k3_xboole_0(B_27,'#skF_2'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1489,c_48])).

tff(c_2172,plain,(
    ! [A_179,B_180,C_181] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_179),B_180,C_181),u1_pre_topc(A_179))
      | ~ r2_hidden(C_181,u1_pre_topc(A_179))
      | ~ r2_hidden(B_180,u1_pre_topc(A_179))
      | ~ m1_subset_1(C_181,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ v2_pre_topc(A_179)
      | ~ l1_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2193,plain,(
    ! [B_27] :
      ( r2_hidden(k3_xboole_0(B_27,'#skF_2'('#skF_5')),u1_pre_topc('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
      | ~ r2_hidden(B_27,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1492,c_2172])).

tff(c_2287,plain,(
    ! [B_185] :
      ( r2_hidden(k3_xboole_0(B_185,'#skF_2'('#skF_5')),u1_pre_topc('#skF_4'))
      | ~ r2_hidden(B_185,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_1489,c_1519,c_2193])).

tff(c_1585,plain,(
    ! [B_27] : k9_subset_1(u1_struct_0('#skF_4'),B_27,'#skF_3'('#skF_5')) = k3_xboole_0(B_27,'#skF_3'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1582,c_48])).

tff(c_1899,plain,(
    ! [A_158] :
      ( r1_tarski('#skF_1'(A_158),u1_pre_topc(A_158))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(A_158),'#skF_2'(A_158),'#skF_3'(A_158)),u1_pre_topc(A_158))
      | v2_pre_topc(A_158)
      | ~ r2_hidden(u1_struct_0(A_158),u1_pre_topc(A_158))
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1902,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_5'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1509,c_1899])).

tff(c_1907,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ r2_hidden(k3_xboole_0('#skF_3'('#skF_5'),'#skF_2'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1520,c_1509,c_162,c_2,c_1585,c_162,c_1509,c_1902])).

tff(c_1908,plain,(
    ~ r2_hidden(k3_xboole_0('#skF_3'('#skF_5'),'#skF_2'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1518,c_1907])).

tff(c_2290,plain,
    ( ~ r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_2287,c_1908])).

tff(c_2302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1582,c_1517,c_2290])).

%------------------------------------------------------------------------------
