%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:51 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  150 (6572 expanded)
%              Number of leaves         :   23 (2104 expanded)
%              Depth                    :   18
%              Number of atoms          :  378 (17990 expanded)
%              Number of equality atoms :   21 (6694 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v2_pre_topc(A) )
             => v2_pre_topc(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tex_2)).

tff(f_50,axiom,(
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

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_44,plain,(
    ~ v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_50,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    ! [A_1] :
      ( r2_hidden(u1_struct_0(A_1),u1_pre_topc(A_1))
      | ~ v2_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    ! [A_15] :
      ( m1_subset_1(u1_pre_topc(A_15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15))))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_63,plain,(
    ! [D_25,B_26,C_27,A_28] :
      ( D_25 = B_26
      | g1_pre_topc(C_27,D_25) != g1_pre_topc(A_28,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_77,plain,(
    ! [B_33,A_34] :
      ( u1_pre_topc('#skF_5') = B_33
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(A_34,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_34))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_63])).

tff(c_81,plain,(
    ! [A_15] :
      ( u1_pre_topc(A_15) = u1_pre_topc('#skF_5')
      | g1_pre_topc(u1_struct_0(A_15),u1_pre_topc(A_15)) != g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc(A_15) ) ),
    inference(resolution,[status(thm)],[c_38,c_77])).

tff(c_89,plain,
    ( u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_81])).

tff(c_91,plain,(
    u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_89])).

tff(c_109,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_38])).

tff(c_115,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_109])).

tff(c_102,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_4')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_48])).

tff(c_42,plain,(
    ! [C_20,A_16,D_21,B_17] :
      ( C_20 = A_16
      | g1_pre_topc(C_20,D_21) != g1_pre_topc(A_16,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_126,plain,(
    ! [C_20,D_21] :
      ( u1_struct_0('#skF_5') = C_20
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_20,D_21)
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_42])).

tff(c_134,plain,(
    ! [C_20,D_21] :
      ( u1_struct_0('#skF_5') = C_20
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_20,D_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_126])).

tff(c_151,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_134])).

tff(c_138,plain,(
    ! [A_38] :
      ( r1_tarski('#skF_1'(A_38),u1_pre_topc(A_38))
      | r2_hidden('#skF_2'(A_38),u1_pre_topc(A_38))
      | v2_pre_topc(A_38)
      | ~ r2_hidden(u1_struct_0(A_38),u1_pre_topc(A_38))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_141,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_138])).

tff(c_146,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_91,c_91,c_141])).

tff(c_147,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_146])).

tff(c_181,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_147])).

tff(c_182,plain,(
    ~ r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_185,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_182])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_185])).

tff(c_191,plain,(
    r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_325,plain,(
    ! [A_55] :
      ( m1_subset_1('#skF_1'(A_55),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55))))
      | m1_subset_1('#skF_2'(A_55),k1_zfmisc_1(u1_struct_0(A_55)))
      | v2_pre_topc(A_55)
      | ~ r2_hidden(u1_struct_0(A_55),u1_pre_topc(A_55))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_328,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_325])).

tff(c_330,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191,c_91,c_151,c_151,c_328])).

tff(c_331,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_330])).

tff(c_332,plain,(
    m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_299,plain,(
    ! [A_53] :
      ( m1_subset_1('#skF_1'(A_53),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53))))
      | m1_subset_1('#skF_3'(A_53),k1_zfmisc_1(u1_struct_0(A_53)))
      | v2_pre_topc(A_53)
      | ~ r2_hidden(u1_struct_0(A_53),u1_pre_topc(A_53))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_302,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_299])).

tff(c_304,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191,c_91,c_151,c_151,c_302])).

tff(c_305,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_304])).

tff(c_306,plain,(
    m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_305])).

tff(c_254,plain,(
    ! [A_48] :
      ( m1_subset_1('#skF_1'(A_48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_48))))
      | r2_hidden('#skF_2'(A_48),u1_pre_topc(A_48))
      | v2_pre_topc(A_48)
      | ~ r2_hidden(u1_struct_0(A_48),u1_pre_topc(A_48))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_257,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_254])).

tff(c_259,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191,c_91,c_151,c_91,c_257])).

tff(c_260,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_259])).

tff(c_261,plain,(
    r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_262,plain,(
    ! [A_49] :
      ( m1_subset_1('#skF_1'(A_49),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_49))))
      | r2_hidden('#skF_3'(A_49),u1_pre_topc(A_49))
      | v2_pre_topc(A_49)
      | ~ r2_hidden(u1_struct_0(A_49),u1_pre_topc(A_49))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_265,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_262])).

tff(c_267,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191,c_91,c_151,c_91,c_265])).

tff(c_268,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_267])).

tff(c_269,plain,(
    r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_409,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_61),B_62,C_63),u1_pre_topc(A_61))
      | ~ r2_hidden(C_63,u1_pre_topc(A_61))
      | ~ r2_hidden(B_62,u1_pre_topc(A_61))
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ v2_pre_topc(A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_382,plain,(
    ! [A_59] :
      ( m1_subset_1('#skF_1'(A_59),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59))))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(A_59),'#skF_2'(A_59),'#skF_3'(A_59)),u1_pre_topc(A_59))
      | v2_pre_topc(A_59)
      | ~ r2_hidden(u1_struct_0(A_59),u1_pre_topc(A_59))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_388,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_5'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_382])).

tff(c_393,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191,c_91,c_151,c_151,c_151,c_388])).

tff(c_394,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_393])).

tff(c_395,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_412,plain,
    ( ~ r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_409,c_395])).

tff(c_434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_332,c_306,c_261,c_269,c_412])).

tff(c_435,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_190,plain,
    ( r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_199,plain,(
    r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_34,plain,(
    ! [A_1,B_10] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_1),B_10),u1_pre_topc(A_1))
      | ~ r1_tarski(B_10,u1_pre_topc(A_1))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v2_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_436,plain,(
    r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_439,plain,(
    ! [A_64] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_64),'#skF_1'(A_64)),u1_pre_topc(A_64))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(A_64),'#skF_2'(A_64),'#skF_3'(A_64)),u1_pre_topc(A_64))
      | v2_pre_topc(A_64)
      | ~ r2_hidden(u1_struct_0(A_64),u1_pre_topc(A_64))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_445,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_5'))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_5'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_439])).

tff(c_450,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191,c_91,c_151,c_436,c_151,c_91,c_151,c_445])).

tff(c_451,plain,(
    ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_450])).

tff(c_480,plain,
    ( ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_451])).

tff(c_484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_435,c_199,c_480])).

tff(c_485,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_486,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_505,plain,(
    ! [A_69] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_69),'#skF_1'(A_69)),u1_pre_topc(A_69))
      | m1_subset_1('#skF_2'(A_69),k1_zfmisc_1(u1_struct_0(A_69)))
      | v2_pre_topc(A_69)
      | ~ r2_hidden(u1_struct_0(A_69),u1_pre_topc(A_69))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_515,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_505])).

tff(c_521,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191,c_91,c_151,c_151,c_151,c_515])).

tff(c_522,plain,(
    ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_486,c_521])).

tff(c_525,plain,
    ( ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_522])).

tff(c_529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_485,c_199,c_525])).

tff(c_530,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_305])).

tff(c_557,plain,(
    ! [A_72] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_72),'#skF_1'(A_72)),u1_pre_topc(A_72))
      | m1_subset_1('#skF_2'(A_72),k1_zfmisc_1(u1_struct_0(A_72)))
      | v2_pre_topc(A_72)
      | ~ r2_hidden(u1_struct_0(A_72),u1_pre_topc(A_72))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_567,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_557])).

tff(c_573,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191,c_91,c_151,c_151,c_151,c_567])).

tff(c_574,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_573])).

tff(c_575,plain,(
    ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_574])).

tff(c_578,plain,
    ( ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_575])).

tff(c_582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_530,c_199,c_578])).

tff(c_584,plain,(
    r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_531,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_305])).

tff(c_591,plain,(
    ! [A_73] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_73),'#skF_1'(A_73)),u1_pre_topc(A_73))
      | m1_subset_1('#skF_3'(A_73),k1_zfmisc_1(u1_struct_0(A_73)))
      | v2_pre_topc(A_73)
      | ~ r2_hidden(u1_struct_0(A_73),u1_pre_topc(A_73))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_601,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_591])).

tff(c_607,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191,c_91,c_151,c_151,c_151,c_601])).

tff(c_608,plain,(
    ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_531,c_607])).

tff(c_610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_608])).

tff(c_611,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_612,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_656,plain,(
    ! [A_79] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_79),'#skF_1'(A_79)),u1_pre_topc(A_79))
      | r2_hidden('#skF_3'(A_79),u1_pre_topc(A_79))
      | v2_pre_topc(A_79)
      | ~ r2_hidden(u1_struct_0(A_79),u1_pre_topc(A_79))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_666,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_656])).

tff(c_672,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191,c_91,c_151,c_91,c_151,c_666])).

tff(c_673,plain,(
    ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_612,c_672])).

tff(c_694,plain,
    ( ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_673])).

tff(c_698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_611,c_199,c_694])).

tff(c_699,plain,(
    m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_700,plain,(
    ~ r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_719,plain,(
    ! [A_84] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(A_84),'#skF_1'(A_84)),u1_pre_topc(A_84))
      | r2_hidden('#skF_2'(A_84),u1_pre_topc(A_84))
      | v2_pre_topc(A_84)
      | ~ r2_hidden(u1_struct_0(A_84),u1_pre_topc(A_84))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_729,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_719])).

tff(c_735,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191,c_91,c_151,c_91,c_151,c_729])).

tff(c_736,plain,(
    ~ r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_700,c_735])).

tff(c_739,plain,
    ( ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_736])).

tff(c_743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_699,c_199,c_739])).

tff(c_745,plain,(
    ~ r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_795,plain,(
    ! [A_91] :
      ( r1_tarski('#skF_1'(A_91),u1_pre_topc(A_91))
      | m1_subset_1('#skF_2'(A_91),k1_zfmisc_1(u1_struct_0(A_91)))
      | v2_pre_topc(A_91)
      | ~ r2_hidden(u1_struct_0(A_91),u1_pre_topc(A_91))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_798,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_795])).

tff(c_800,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191,c_91,c_151,c_91,c_798])).

tff(c_801,plain,(
    m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_745,c_800])).

tff(c_788,plain,(
    ! [A_90] :
      ( r1_tarski('#skF_1'(A_90),u1_pre_topc(A_90))
      | m1_subset_1('#skF_3'(A_90),k1_zfmisc_1(u1_struct_0(A_90)))
      | v2_pre_topc(A_90)
      | ~ r2_hidden(u1_struct_0(A_90),u1_pre_topc(A_90))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_791,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_788])).

tff(c_793,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191,c_91,c_151,c_91,c_791])).

tff(c_794,plain,(
    m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_745,c_793])).

tff(c_744,plain,(
    r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_746,plain,(
    ! [A_85] :
      ( r1_tarski('#skF_1'(A_85),u1_pre_topc(A_85))
      | r2_hidden('#skF_3'(A_85),u1_pre_topc(A_85))
      | v2_pre_topc(A_85)
      | ~ r2_hidden(u1_struct_0(A_85),u1_pre_topc(A_85))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_755,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_5'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_746])).

tff(c_766,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191,c_151,c_91,c_91,c_755])).

tff(c_767,plain,(
    r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_745,c_766])).

tff(c_952,plain,(
    ! [A_105,B_106,C_107] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_105),B_106,C_107),u1_pre_topc(A_105))
      | ~ r2_hidden(C_107,u1_pre_topc(A_105))
      | ~ r2_hidden(B_106,u1_pre_topc(A_105))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ v2_pre_topc(A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_913,plain,(
    ! [A_102] :
      ( r1_tarski('#skF_1'(A_102),u1_pre_topc(A_102))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(A_102),'#skF_2'(A_102),'#skF_3'(A_102)),u1_pre_topc(A_102))
      | v2_pre_topc(A_102)
      | ~ r2_hidden(u1_struct_0(A_102),u1_pre_topc(A_102))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_919,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_5'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5')
    | ~ r2_hidden(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_913])).

tff(c_924,plain,
    ( r1_tarski('#skF_1'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4'))
    | v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_191,c_91,c_151,c_151,c_91,c_919])).

tff(c_925,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5'),'#skF_3'('#skF_5')),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_745,c_924])).

tff(c_963,plain,
    ( ~ r2_hidden('#skF_3'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_5'),u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_3'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_952,c_925])).

tff(c_979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_801,c_794,c_744,c_767,c_963])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.46  
% 3.28/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.46  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3
% 3.28/1.46  
% 3.28/1.46  %Foreground sorts:
% 3.28/1.46  
% 3.28/1.46  
% 3.28/1.46  %Background operators:
% 3.28/1.46  
% 3.28/1.46  
% 3.28/1.46  %Foreground operators:
% 3.28/1.46  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.28/1.46  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.28/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.46  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.28/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.28/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.28/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.28/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.46  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.28/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.46  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.28/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.28/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.28/1.46  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.28/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.46  
% 3.43/1.49  tff(f_75, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v2_pre_topc(A)) => v2_pre_topc(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tex_2)).
% 3.43/1.49  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 3.43/1.49  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.43/1.49  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 3.43/1.49  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.43/1.49  tff(c_46, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.43/1.49  tff(c_44, plain, (~v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.43/1.49  tff(c_50, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.43/1.49  tff(c_36, plain, (![A_1]: (r2_hidden(u1_struct_0(A_1), u1_pre_topc(A_1)) | ~v2_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_38, plain, (![A_15]: (m1_subset_1(u1_pre_topc(A_15), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15)))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.43/1.49  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.43/1.49  tff(c_63, plain, (![D_25, B_26, C_27, A_28]: (D_25=B_26 | g1_pre_topc(C_27, D_25)!=g1_pre_topc(A_28, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_28))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.43/1.49  tff(c_77, plain, (![B_33, A_34]: (u1_pre_topc('#skF_5')=B_33 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(A_34, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(A_34))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_63])).
% 3.43/1.49  tff(c_81, plain, (![A_15]: (u1_pre_topc(A_15)=u1_pre_topc('#skF_5') | g1_pre_topc(u1_struct_0(A_15), u1_pre_topc(A_15))!=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~l1_pre_topc(A_15))), inference(resolution, [status(thm)], [c_38, c_77])).
% 3.43/1.49  tff(c_89, plain, (u1_pre_topc('#skF_5')=u1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_81])).
% 3.43/1.49  tff(c_91, plain, (u1_pre_topc('#skF_5')=u1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_89])).
% 3.43/1.49  tff(c_109, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_38])).
% 3.43/1.49  tff(c_115, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_109])).
% 3.43/1.49  tff(c_102, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_4'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_48])).
% 3.43/1.49  tff(c_42, plain, (![C_20, A_16, D_21, B_17]: (C_20=A_16 | g1_pre_topc(C_20, D_21)!=g1_pre_topc(A_16, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.43/1.49  tff(c_126, plain, (![C_20, D_21]: (u1_struct_0('#skF_5')=C_20 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(C_20, D_21) | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))))), inference(superposition, [status(thm), theory('equality')], [c_102, c_42])).
% 3.43/1.49  tff(c_134, plain, (![C_20, D_21]: (u1_struct_0('#skF_5')=C_20 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(C_20, D_21))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_126])).
% 3.43/1.49  tff(c_151, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_134])).
% 3.43/1.49  tff(c_138, plain, (![A_38]: (r1_tarski('#skF_1'(A_38), u1_pre_topc(A_38)) | r2_hidden('#skF_2'(A_38), u1_pre_topc(A_38)) | v2_pre_topc(A_38) | ~r2_hidden(u1_struct_0(A_38), u1_pre_topc(A_38)) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_141, plain, (r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_5')) | r2_hidden('#skF_2'('#skF_5'), u1_pre_topc('#skF_5')) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_4')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_138])).
% 3.43/1.49  tff(c_146, plain, (r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_4')) | r2_hidden('#skF_2'('#skF_5'), u1_pre_topc('#skF_4')) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_91, c_91, c_141])).
% 3.43/1.49  tff(c_147, plain, (r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_4')) | r2_hidden('#skF_2'('#skF_5'), u1_pre_topc('#skF_4')) | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_146])).
% 3.43/1.49  tff(c_181, plain, (r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_4')) | r2_hidden('#skF_2'('#skF_5'), u1_pre_topc('#skF_4')) | ~r2_hidden(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_147])).
% 3.43/1.49  tff(c_182, plain, (~r2_hidden(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(splitLeft, [status(thm)], [c_181])).
% 3.43/1.49  tff(c_185, plain, (~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_182])).
% 3.43/1.49  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_185])).
% 3.43/1.49  tff(c_191, plain, (r2_hidden(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_181])).
% 3.43/1.49  tff(c_325, plain, (![A_55]: (m1_subset_1('#skF_1'(A_55), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_55)))) | m1_subset_1('#skF_2'(A_55), k1_zfmisc_1(u1_struct_0(A_55))) | v2_pre_topc(A_55) | ~r2_hidden(u1_struct_0(A_55), u1_pre_topc(A_55)) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_328, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_151, c_325])).
% 3.43/1.49  tff(c_330, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191, c_91, c_151, c_151, c_328])).
% 3.43/1.49  tff(c_331, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_330])).
% 3.43/1.49  tff(c_332, plain, (m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_331])).
% 3.43/1.49  tff(c_299, plain, (![A_53]: (m1_subset_1('#skF_1'(A_53), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53)))) | m1_subset_1('#skF_3'(A_53), k1_zfmisc_1(u1_struct_0(A_53))) | v2_pre_topc(A_53) | ~r2_hidden(u1_struct_0(A_53), u1_pre_topc(A_53)) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_302, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_151, c_299])).
% 3.43/1.49  tff(c_304, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191, c_91, c_151, c_151, c_302])).
% 3.43/1.49  tff(c_305, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_304])).
% 3.43/1.49  tff(c_306, plain, (m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_305])).
% 3.43/1.49  tff(c_254, plain, (![A_48]: (m1_subset_1('#skF_1'(A_48), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_48)))) | r2_hidden('#skF_2'(A_48), u1_pre_topc(A_48)) | v2_pre_topc(A_48) | ~r2_hidden(u1_struct_0(A_48), u1_pre_topc(A_48)) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_257, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | r2_hidden('#skF_2'('#skF_5'), u1_pre_topc('#skF_5')) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_151, c_254])).
% 3.43/1.49  tff(c_259, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | r2_hidden('#skF_2'('#skF_5'), u1_pre_topc('#skF_4')) | v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191, c_91, c_151, c_91, c_257])).
% 3.43/1.49  tff(c_260, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | r2_hidden('#skF_2'('#skF_5'), u1_pre_topc('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_259])).
% 3.43/1.49  tff(c_261, plain, (r2_hidden('#skF_2'('#skF_5'), u1_pre_topc('#skF_4'))), inference(splitLeft, [status(thm)], [c_260])).
% 3.43/1.49  tff(c_262, plain, (![A_49]: (m1_subset_1('#skF_1'(A_49), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_49)))) | r2_hidden('#skF_3'(A_49), u1_pre_topc(A_49)) | v2_pre_topc(A_49) | ~r2_hidden(u1_struct_0(A_49), u1_pre_topc(A_49)) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_265, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | r2_hidden('#skF_3'('#skF_5'), u1_pre_topc('#skF_5')) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_151, c_262])).
% 3.43/1.49  tff(c_267, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | r2_hidden('#skF_3'('#skF_5'), u1_pre_topc('#skF_4')) | v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191, c_91, c_151, c_91, c_265])).
% 3.43/1.49  tff(c_268, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | r2_hidden('#skF_3'('#skF_5'), u1_pre_topc('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_267])).
% 3.43/1.49  tff(c_269, plain, (r2_hidden('#skF_3'('#skF_5'), u1_pre_topc('#skF_4'))), inference(splitLeft, [status(thm)], [c_268])).
% 3.43/1.49  tff(c_409, plain, (![A_61, B_62, C_63]: (r2_hidden(k9_subset_1(u1_struct_0(A_61), B_62, C_63), u1_pre_topc(A_61)) | ~r2_hidden(C_63, u1_pre_topc(A_61)) | ~r2_hidden(B_62, u1_pre_topc(A_61)) | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~v2_pre_topc(A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_382, plain, (![A_59]: (m1_subset_1('#skF_1'(A_59), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59)))) | ~r2_hidden(k9_subset_1(u1_struct_0(A_59), '#skF_2'(A_59), '#skF_3'(A_59)), u1_pre_topc(A_59)) | v2_pre_topc(A_59) | ~r2_hidden(u1_struct_0(A_59), u1_pre_topc(A_59)) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_388, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) | ~r2_hidden(k9_subset_1(u1_struct_0('#skF_5'), '#skF_2'('#skF_5'), '#skF_3'('#skF_5')), u1_pre_topc('#skF_4')) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_382])).
% 3.43/1.49  tff(c_393, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~r2_hidden(k9_subset_1(u1_struct_0('#skF_4'), '#skF_2'('#skF_5'), '#skF_3'('#skF_5')), u1_pre_topc('#skF_4')) | v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191, c_91, c_151, c_151, c_151, c_388])).
% 3.43/1.49  tff(c_394, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~r2_hidden(k9_subset_1(u1_struct_0('#skF_4'), '#skF_2'('#skF_5'), '#skF_3'('#skF_5')), u1_pre_topc('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_393])).
% 3.43/1.49  tff(c_395, plain, (~r2_hidden(k9_subset_1(u1_struct_0('#skF_4'), '#skF_2'('#skF_5'), '#skF_3'('#skF_5')), u1_pre_topc('#skF_4'))), inference(splitLeft, [status(thm)], [c_394])).
% 3.43/1.49  tff(c_412, plain, (~r2_hidden('#skF_3'('#skF_5'), u1_pre_topc('#skF_4')) | ~r2_hidden('#skF_2'('#skF_5'), u1_pre_topc('#skF_4')) | ~m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_409, c_395])).
% 3.43/1.49  tff(c_434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_332, c_306, c_261, c_269, c_412])).
% 3.43/1.49  tff(c_435, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_394])).
% 3.43/1.49  tff(c_190, plain, (r2_hidden('#skF_2'('#skF_5'), u1_pre_topc('#skF_4')) | r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_181])).
% 3.43/1.49  tff(c_199, plain, (r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_4'))), inference(splitLeft, [status(thm)], [c_190])).
% 3.43/1.49  tff(c_34, plain, (![A_1, B_10]: (r2_hidden(k5_setfam_1(u1_struct_0(A_1), B_10), u1_pre_topc(A_1)) | ~r1_tarski(B_10, u1_pre_topc(A_1)) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v2_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_436, plain, (r2_hidden(k9_subset_1(u1_struct_0('#skF_4'), '#skF_2'('#skF_5'), '#skF_3'('#skF_5')), u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_394])).
% 3.43/1.49  tff(c_439, plain, (![A_64]: (~r2_hidden(k5_setfam_1(u1_struct_0(A_64), '#skF_1'(A_64)), u1_pre_topc(A_64)) | ~r2_hidden(k9_subset_1(u1_struct_0(A_64), '#skF_2'(A_64), '#skF_3'(A_64)), u1_pre_topc(A_64)) | v2_pre_topc(A_64) | ~r2_hidden(u1_struct_0(A_64), u1_pre_topc(A_64)) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_445, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_5')) | ~r2_hidden(k9_subset_1(u1_struct_0('#skF_5'), '#skF_2'('#skF_5'), '#skF_3'('#skF_5')), u1_pre_topc('#skF_4')) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_439])).
% 3.43/1.49  tff(c_450, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4')) | v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191, c_91, c_151, c_436, c_151, c_91, c_151, c_445])).
% 3.43/1.49  tff(c_451, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_450])).
% 3.43/1.49  tff(c_480, plain, (~r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_4')) | ~m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34, c_451])).
% 3.43/1.49  tff(c_484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_435, c_199, c_480])).
% 3.43/1.49  tff(c_485, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_331])).
% 3.43/1.49  tff(c_486, plain, (~m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_331])).
% 3.43/1.49  tff(c_505, plain, (![A_69]: (~r2_hidden(k5_setfam_1(u1_struct_0(A_69), '#skF_1'(A_69)), u1_pre_topc(A_69)) | m1_subset_1('#skF_2'(A_69), k1_zfmisc_1(u1_struct_0(A_69))) | v2_pre_topc(A_69) | ~r2_hidden(u1_struct_0(A_69), u1_pre_topc(A_69)) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_515, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4')) | m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_505])).
% 3.43/1.49  tff(c_521, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4')) | m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191, c_91, c_151, c_151, c_151, c_515])).
% 3.43/1.49  tff(c_522, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_486, c_521])).
% 3.43/1.49  tff(c_525, plain, (~r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_4')) | ~m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34, c_522])).
% 3.43/1.49  tff(c_529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_485, c_199, c_525])).
% 3.43/1.49  tff(c_530, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_305])).
% 3.43/1.49  tff(c_557, plain, (![A_72]: (~r2_hidden(k5_setfam_1(u1_struct_0(A_72), '#skF_1'(A_72)), u1_pre_topc(A_72)) | m1_subset_1('#skF_2'(A_72), k1_zfmisc_1(u1_struct_0(A_72))) | v2_pre_topc(A_72) | ~r2_hidden(u1_struct_0(A_72), u1_pre_topc(A_72)) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_567, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4')) | m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_557])).
% 3.43/1.49  tff(c_573, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4')) | m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191, c_91, c_151, c_151, c_151, c_567])).
% 3.43/1.49  tff(c_574, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4')) | m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_573])).
% 3.43/1.49  tff(c_575, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4'))), inference(splitLeft, [status(thm)], [c_574])).
% 3.43/1.49  tff(c_578, plain, (~r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_4')) | ~m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34, c_575])).
% 3.43/1.49  tff(c_582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_530, c_199, c_578])).
% 3.43/1.49  tff(c_584, plain, (r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_574])).
% 3.43/1.49  tff(c_531, plain, (~m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_305])).
% 3.43/1.49  tff(c_591, plain, (![A_73]: (~r2_hidden(k5_setfam_1(u1_struct_0(A_73), '#skF_1'(A_73)), u1_pre_topc(A_73)) | m1_subset_1('#skF_3'(A_73), k1_zfmisc_1(u1_struct_0(A_73))) | v2_pre_topc(A_73) | ~r2_hidden(u1_struct_0(A_73), u1_pre_topc(A_73)) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_601, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4')) | m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_591])).
% 3.43/1.49  tff(c_607, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4')) | m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191, c_91, c_151, c_151, c_151, c_601])).
% 3.43/1.49  tff(c_608, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_531, c_607])).
% 3.43/1.49  tff(c_610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_584, c_608])).
% 3.43/1.49  tff(c_611, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_268])).
% 3.43/1.49  tff(c_612, plain, (~r2_hidden('#skF_3'('#skF_5'), u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_268])).
% 3.43/1.49  tff(c_656, plain, (![A_79]: (~r2_hidden(k5_setfam_1(u1_struct_0(A_79), '#skF_1'(A_79)), u1_pre_topc(A_79)) | r2_hidden('#skF_3'(A_79), u1_pre_topc(A_79)) | v2_pre_topc(A_79) | ~r2_hidden(u1_struct_0(A_79), u1_pre_topc(A_79)) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_666, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4')) | r2_hidden('#skF_3'('#skF_5'), u1_pre_topc('#skF_5')) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_656])).
% 3.43/1.49  tff(c_672, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4')) | r2_hidden('#skF_3'('#skF_5'), u1_pre_topc('#skF_4')) | v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191, c_91, c_151, c_91, c_151, c_666])).
% 3.43/1.49  tff(c_673, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_612, c_672])).
% 3.43/1.49  tff(c_694, plain, (~r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_4')) | ~m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34, c_673])).
% 3.43/1.49  tff(c_698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_611, c_199, c_694])).
% 3.43/1.49  tff(c_699, plain, (m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_260])).
% 3.43/1.49  tff(c_700, plain, (~r2_hidden('#skF_2'('#skF_5'), u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_260])).
% 3.43/1.49  tff(c_719, plain, (![A_84]: (~r2_hidden(k5_setfam_1(u1_struct_0(A_84), '#skF_1'(A_84)), u1_pre_topc(A_84)) | r2_hidden('#skF_2'(A_84), u1_pre_topc(A_84)) | v2_pre_topc(A_84) | ~r2_hidden(u1_struct_0(A_84), u1_pre_topc(A_84)) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_729, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_5'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4')) | r2_hidden('#skF_2'('#skF_5'), u1_pre_topc('#skF_5')) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_719])).
% 3.43/1.49  tff(c_735, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4')) | r2_hidden('#skF_2'('#skF_5'), u1_pre_topc('#skF_4')) | v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191, c_91, c_151, c_91, c_151, c_729])).
% 3.43/1.49  tff(c_736, plain, (~r2_hidden(k5_setfam_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5')), u1_pre_topc('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_700, c_735])).
% 3.43/1.49  tff(c_739, plain, (~r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_4')) | ~m1_subset_1('#skF_1'('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34, c_736])).
% 3.43/1.49  tff(c_743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_699, c_199, c_739])).
% 3.43/1.49  tff(c_745, plain, (~r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_190])).
% 3.43/1.49  tff(c_795, plain, (![A_91]: (r1_tarski('#skF_1'(A_91), u1_pre_topc(A_91)) | m1_subset_1('#skF_2'(A_91), k1_zfmisc_1(u1_struct_0(A_91))) | v2_pre_topc(A_91) | ~r2_hidden(u1_struct_0(A_91), u1_pre_topc(A_91)) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_798, plain, (r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_5')) | m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_151, c_795])).
% 3.43/1.49  tff(c_800, plain, (r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_4')) | m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191, c_91, c_151, c_91, c_798])).
% 3.43/1.49  tff(c_801, plain, (m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_745, c_800])).
% 3.43/1.49  tff(c_788, plain, (![A_90]: (r1_tarski('#skF_1'(A_90), u1_pre_topc(A_90)) | m1_subset_1('#skF_3'(A_90), k1_zfmisc_1(u1_struct_0(A_90))) | v2_pre_topc(A_90) | ~r2_hidden(u1_struct_0(A_90), u1_pre_topc(A_90)) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_791, plain, (r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_5')) | m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_151, c_788])).
% 3.43/1.49  tff(c_793, plain, (r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_4')) | m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191, c_91, c_151, c_91, c_791])).
% 3.43/1.49  tff(c_794, plain, (m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_745, c_793])).
% 3.43/1.49  tff(c_744, plain, (r2_hidden('#skF_2'('#skF_5'), u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_190])).
% 3.43/1.49  tff(c_746, plain, (![A_85]: (r1_tarski('#skF_1'(A_85), u1_pre_topc(A_85)) | r2_hidden('#skF_3'(A_85), u1_pre_topc(A_85)) | v2_pre_topc(A_85) | ~r2_hidden(u1_struct_0(A_85), u1_pre_topc(A_85)) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_755, plain, (r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_5')) | r2_hidden('#skF_3'('#skF_5'), u1_pre_topc('#skF_5')) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_4')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_746])).
% 3.43/1.49  tff(c_766, plain, (r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_4')) | r2_hidden('#skF_3'('#skF_5'), u1_pre_topc('#skF_4')) | v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191, c_151, c_91, c_91, c_755])).
% 3.43/1.49  tff(c_767, plain, (r2_hidden('#skF_3'('#skF_5'), u1_pre_topc('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_745, c_766])).
% 3.43/1.49  tff(c_952, plain, (![A_105, B_106, C_107]: (r2_hidden(k9_subset_1(u1_struct_0(A_105), B_106, C_107), u1_pre_topc(A_105)) | ~r2_hidden(C_107, u1_pre_topc(A_105)) | ~r2_hidden(B_106, u1_pre_topc(A_105)) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~v2_pre_topc(A_105) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_913, plain, (![A_102]: (r1_tarski('#skF_1'(A_102), u1_pre_topc(A_102)) | ~r2_hidden(k9_subset_1(u1_struct_0(A_102), '#skF_2'(A_102), '#skF_3'(A_102)), u1_pre_topc(A_102)) | v2_pre_topc(A_102) | ~r2_hidden(u1_struct_0(A_102), u1_pre_topc(A_102)) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.49  tff(c_919, plain, (r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_5')) | ~r2_hidden(k9_subset_1(u1_struct_0('#skF_5'), '#skF_2'('#skF_5'), '#skF_3'('#skF_5')), u1_pre_topc('#skF_4')) | v2_pre_topc('#skF_5') | ~r2_hidden(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_913])).
% 3.43/1.49  tff(c_924, plain, (r1_tarski('#skF_1'('#skF_5'), u1_pre_topc('#skF_4')) | ~r2_hidden(k9_subset_1(u1_struct_0('#skF_4'), '#skF_2'('#skF_5'), '#skF_3'('#skF_5')), u1_pre_topc('#skF_4')) | v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_191, c_91, c_151, c_151, c_91, c_919])).
% 3.43/1.49  tff(c_925, plain, (~r2_hidden(k9_subset_1(u1_struct_0('#skF_4'), '#skF_2'('#skF_5'), '#skF_3'('#skF_5')), u1_pre_topc('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_745, c_924])).
% 3.43/1.49  tff(c_963, plain, (~r2_hidden('#skF_3'('#skF_5'), u1_pre_topc('#skF_4')) | ~r2_hidden('#skF_2'('#skF_5'), u1_pre_topc('#skF_4')) | ~m1_subset_1('#skF_3'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_952, c_925])).
% 3.43/1.49  tff(c_979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_801, c_794, c_744, c_767, c_963])).
% 3.43/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.49  
% 3.43/1.49  Inference rules
% 3.43/1.49  ----------------------
% 3.43/1.49  #Ref     : 8
% 3.43/1.49  #Sup     : 149
% 3.43/1.49  #Fact    : 0
% 3.43/1.49  #Define  : 0
% 3.43/1.49  #Split   : 9
% 3.43/1.49  #Chain   : 0
% 3.43/1.49  #Close   : 0
% 3.43/1.49  
% 3.43/1.49  Ordering : KBO
% 3.43/1.49  
% 3.43/1.49  Simplification rules
% 3.43/1.49  ----------------------
% 3.43/1.49  #Subsume      : 32
% 3.43/1.49  #Demod        : 569
% 3.43/1.49  #Tautology    : 88
% 3.43/1.49  #SimpNegUnit  : 71
% 3.43/1.49  #BackRed      : 5
% 3.43/1.49  
% 3.43/1.49  #Partial instantiations: 0
% 3.43/1.49  #Strategies tried      : 1
% 3.43/1.49  
% 3.43/1.49  Timing (in seconds)
% 3.43/1.49  ----------------------
% 3.43/1.49  Preprocessing        : 0.29
% 3.43/1.49  Parsing              : 0.15
% 3.43/1.49  CNF conversion       : 0.02
% 3.43/1.49  Main loop            : 0.41
% 3.43/1.49  Inferencing          : 0.14
% 3.43/1.49  Reduction            : 0.15
% 3.43/1.49  Demodulation         : 0.11
% 3.43/1.49  BG Simplification    : 0.02
% 3.43/1.49  Subsumption          : 0.07
% 3.43/1.49  Abstraction          : 0.02
% 3.43/1.49  MUC search           : 0.00
% 3.43/1.49  Cooper               : 0.00
% 3.43/1.49  Total                : 0.75
% 3.43/1.49  Index Insertion      : 0.00
% 3.43/1.49  Index Deletion       : 0.00
% 3.43/1.49  Index Matching       : 0.00
% 3.43/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
