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
% DateTime   : Thu Dec  3 10:19:47 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 359 expanded)
%              Number of leaves         :   28 ( 148 expanded)
%              Depth                    :   19
%              Number of atoms          :  359 (1746 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( r2_orders_2(A,B,C)
                     => r1_tarski(k3_orders_2(A,D,B),k3_orders_2(A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( ( r2_orders_2(A,B,C)
                        & r1_orders_2(A,C,D) )
                      | ( r1_orders_2(A,B,C)
                        & r2_orders_2(A,C,D) ) )
                   => r2_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).

tff(c_28,plain,(
    ~ r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_1'(A_62,B_63),A_62)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,(
    ! [A_62] : r1_tarski(A_62,A_62) ),
    inference(resolution,[status(thm)],[c_48,c_4])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_44,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_42,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_40,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_38,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,(
    ! [C_65,B_66,A_67] :
      ( r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_1,B_2,B_66] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_66)
      | ~ r1_tarski(A_1,B_66)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_55])).

tff(c_115,plain,(
    ! [A_88,B_89,C_90] :
      ( m1_subset_1(k3_orders_2(A_88,B_89,C_90),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(C_90,u1_struct_0(A_88))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_orders_2(A_88)
      | ~ v5_orders_2(A_88)
      | ~ v4_orders_2(A_88)
      | ~ v3_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( m1_subset_1(A_6,C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_210,plain,(
    ! [A_100,A_101,B_102,C_103] :
      ( m1_subset_1(A_100,u1_struct_0(A_101))
      | ~ r2_hidden(A_100,k3_orders_2(A_101,B_102,C_103))
      | ~ m1_subset_1(C_103,u1_struct_0(A_101))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_orders_2(A_101)
      | ~ v5_orders_2(A_101)
      | ~ v4_orders_2(A_101)
      | ~ v3_orders_2(A_101)
      | v2_struct_0(A_101) ) ),
    inference(resolution,[status(thm)],[c_115,c_8])).

tff(c_1212,plain,(
    ! [A_252,B_250,B_251,C_253,A_249] :
      ( m1_subset_1('#skF_1'(A_252,B_251),u1_struct_0(A_249))
      | ~ m1_subset_1(C_253,u1_struct_0(A_249))
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_orders_2(A_249)
      | ~ v5_orders_2(A_249)
      | ~ v4_orders_2(A_249)
      | ~ v3_orders_2(A_249)
      | v2_struct_0(A_249)
      | ~ r1_tarski(A_252,k3_orders_2(A_249,B_250,C_253))
      | r1_tarski(A_252,B_251) ) ),
    inference(resolution,[status(thm)],[c_58,c_210])).

tff(c_1216,plain,(
    ! [A_252,B_251,C_253] :
      ( m1_subset_1('#skF_1'(A_252,B_251),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_253,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_252,k3_orders_2('#skF_2','#skF_5',C_253))
      | r1_tarski(A_252,B_251) ) ),
    inference(resolution,[status(thm)],[c_32,c_1212])).

tff(c_1220,plain,(
    ! [A_252,B_251,C_253] :
      ( m1_subset_1('#skF_1'(A_252,B_251),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_253,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_252,k3_orders_2('#skF_2','#skF_5',C_253))
      | r1_tarski(A_252,B_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_1216])).

tff(c_1259,plain,(
    ! [A_259,B_260,C_261] :
      ( m1_subset_1('#skF_1'(A_259,B_260),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_261,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_259,k3_orders_2('#skF_2','#skF_5',C_261))
      | r1_tarski(A_259,B_260) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1220])).

tff(c_1273,plain,(
    ! [C_261,B_260] :
      ( m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_261),B_260),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_261,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_261),B_260) ) ),
    inference(resolution,[status(thm)],[c_53,c_1259])).

tff(c_1107,plain,(
    ! [A_241,B_242,C_243,B_244] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_241,B_242,C_243),B_244),u1_struct_0(A_241))
      | ~ m1_subset_1(C_243,u1_struct_0(A_241))
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_orders_2(A_241)
      | ~ v5_orders_2(A_241)
      | ~ v4_orders_2(A_241)
      | ~ v3_orders_2(A_241)
      | v2_struct_0(A_241)
      | r1_tarski(k3_orders_2(A_241,B_242,C_243),B_244) ) ),
    inference(resolution,[status(thm)],[c_6,c_210])).

tff(c_357,plain,(
    ! [B_120,D_121,A_122,C_123] :
      ( r2_hidden(B_120,D_121)
      | ~ r2_hidden(B_120,k3_orders_2(A_122,D_121,C_123))
      | ~ m1_subset_1(D_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_subset_1(C_123,u1_struct_0(A_122))
      | ~ m1_subset_1(B_120,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | ~ v5_orders_2(A_122)
      | ~ v4_orders_2(A_122)
      | ~ v3_orders_2(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_365,plain,(
    ! [A_122,D_121,C_123,B_2] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_122,D_121,C_123),B_2),D_121)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_subset_1(C_123,u1_struct_0(A_122))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_122,D_121,C_123),B_2),u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | ~ v5_orders_2(A_122)
      | ~ v4_orders_2(A_122)
      | ~ v3_orders_2(A_122)
      | v2_struct_0(A_122)
      | r1_tarski(k3_orders_2(A_122,D_121,C_123),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_357])).

tff(c_1184,plain,(
    ! [A_245,B_246,C_247,B_248] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_245,B_246,C_247),B_248),B_246)
      | ~ m1_subset_1(C_247,u1_struct_0(A_245))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_orders_2(A_245)
      | ~ v5_orders_2(A_245)
      | ~ v4_orders_2(A_245)
      | ~ v3_orders_2(A_245)
      | v2_struct_0(A_245)
      | r1_tarski(k3_orders_2(A_245,B_246,C_247),B_248) ) ),
    inference(resolution,[status(thm)],[c_1107,c_365])).

tff(c_60,plain,(
    ! [A_70,C_71,B_72] :
      ( m1_subset_1(A_70,C_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(C_71))
      | ~ r2_hidden(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,(
    ! [A_70] :
      ( m1_subset_1(A_70,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_70,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_60])).

tff(c_777,plain,(
    ! [A_170,D_171,C_172,B_173] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_170,D_171,C_172),B_173),D_171)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ m1_subset_1(C_172,u1_struct_0(A_170))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_170,D_171,C_172),B_173),u1_struct_0(A_170))
      | ~ l1_orders_2(A_170)
      | ~ v5_orders_2(A_170)
      | ~ v4_orders_2(A_170)
      | ~ v3_orders_2(A_170)
      | v2_struct_0(A_170)
      | r1_tarski(k3_orders_2(A_170,D_171,C_172),B_173) ) ),
    inference(resolution,[status(thm)],[c_6,c_357])).

tff(c_780,plain,(
    ! [D_171,C_172,B_173] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_171,C_172),B_173),D_171)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_172,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2',D_171,C_172),B_173)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_171,C_172),B_173),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_63,c_777])).

tff(c_783,plain,(
    ! [D_171,C_172,B_173] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_171,C_172),B_173),D_171)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_172,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2',D_171,C_172),B_173)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_171,C_172),B_173),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_780])).

tff(c_784,plain,(
    ! [D_171,C_172,B_173] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_171,C_172),B_173),D_171)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_172,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2',D_171,C_172),B_173)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_171,C_172),B_173),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_783])).

tff(c_1187,plain,(
    ! [C_247,B_248] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_247),B_248),'#skF_5')
      | ~ m1_subset_1(C_247,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_247),B_248) ) ),
    inference(resolution,[status(thm)],[c_1184,c_784])).

tff(c_1205,plain,(
    ! [C_247,B_248] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_247),B_248),'#skF_5')
      | ~ m1_subset_1(C_247,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_247),B_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_32,c_1187])).

tff(c_1222,plain,(
    ! [C_254,B_255] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_254),B_255),'#skF_5')
      | ~ m1_subset_1(C_254,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_254),B_255) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1205])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1234,plain,(
    ! [C_254,B_255,B_2] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_254),B_255),B_2)
      | ~ r1_tarski('#skF_5',B_2)
      | ~ m1_subset_1(C_254,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_254),B_255) ) ),
    inference(resolution,[status(thm)],[c_1222,c_2])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1289,plain,(
    ! [C_265,B_266] :
      ( m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_265),B_266),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_265,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_265),B_266) ) ),
    inference(resolution,[status(thm)],[c_53,c_1259])).

tff(c_468,plain,(
    ! [A_140,B_141,C_142,D_143] :
      ( r2_orders_2(A_140,B_141,C_142)
      | ~ r2_hidden(B_141,k3_orders_2(A_140,D_143,C_142))
      | ~ m1_subset_1(D_143,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_subset_1(C_142,u1_struct_0(A_140))
      | ~ m1_subset_1(B_141,u1_struct_0(A_140))
      | ~ l1_orders_2(A_140)
      | ~ v5_orders_2(A_140)
      | ~ v4_orders_2(A_140)
      | ~ v3_orders_2(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_476,plain,(
    ! [A_140,D_143,C_142,B_2] :
      ( r2_orders_2(A_140,'#skF_1'(k3_orders_2(A_140,D_143,C_142),B_2),C_142)
      | ~ m1_subset_1(D_143,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_subset_1(C_142,u1_struct_0(A_140))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_140,D_143,C_142),B_2),u1_struct_0(A_140))
      | ~ l1_orders_2(A_140)
      | ~ v5_orders_2(A_140)
      | ~ v4_orders_2(A_140)
      | ~ v3_orders_2(A_140)
      | v2_struct_0(A_140)
      | r1_tarski(k3_orders_2(A_140,D_143,C_142),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_468])).

tff(c_1291,plain,(
    ! [C_265,B_266] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_265),B_266),C_265)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_265,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_265),B_266) ) ),
    inference(resolution,[status(thm)],[c_1289,c_476])).

tff(c_1318,plain,(
    ! [C_265,B_266] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_265),B_266),C_265)
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_265,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_265),B_266) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_32,c_1291])).

tff(c_1332,plain,(
    ! [C_267,B_268] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_267),B_268),C_267)
      | ~ m1_subset_1(C_267,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_267),B_268) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1318])).

tff(c_30,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_78,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_orders_2(A_81,B_82,C_83)
      | ~ r2_orders_2(A_81,B_82,C_83)
      | ~ m1_subset_1(C_83,u1_struct_0(A_81))
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l1_orders_2(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_80,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_78])).

tff(c_83,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_80])).

tff(c_219,plain,(
    ! [A_104,C_105,D_106,B_107] :
      ( ~ r1_orders_2(A_104,C_105,D_106)
      | ~ r2_orders_2(A_104,B_107,C_105)
      | r2_orders_2(A_104,B_107,D_106)
      | ~ m1_subset_1(D_106,u1_struct_0(A_104))
      | ~ m1_subset_1(C_105,u1_struct_0(A_104))
      | ~ m1_subset_1(B_107,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104)
      | ~ v5_orders_2(A_104)
      | ~ v4_orders_2(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_221,plain,(
    ! [B_107] :
      ( ~ r2_orders_2('#skF_2',B_107,'#skF_3')
      | r2_orders_2('#skF_2',B_107,'#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_83,c_219])).

tff(c_287,plain,(
    ! [B_114] :
      ( ~ r2_orders_2('#skF_2',B_114,'#skF_3')
      | r2_orders_2('#skF_2',B_114,'#skF_4')
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_221])).

tff(c_297,plain,(
    ! [A_70] :
      ( ~ r2_orders_2('#skF_2',A_70,'#skF_3')
      | r2_orders_2('#skF_2',A_70,'#skF_4')
      | ~ r2_hidden(A_70,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_63,c_287])).

tff(c_1339,plain,(
    ! [B_268] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),B_268),'#skF_4')
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),B_268),'#skF_5')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),B_268) ) ),
    inference(resolution,[status(thm)],[c_1332,c_297])).

tff(c_1448,plain,(
    ! [B_278] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),B_278),'#skF_4')
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),B_278),'#skF_5')
      | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),B_278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1339])).

tff(c_649,plain,(
    ! [B_151,A_152,D_153,C_154] :
      ( r2_hidden(B_151,k3_orders_2(A_152,D_153,C_154))
      | ~ r2_hidden(B_151,D_153)
      | ~ r2_orders_2(A_152,B_151,C_154)
      | ~ m1_subset_1(D_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ m1_subset_1(C_154,u1_struct_0(A_152))
      | ~ m1_subset_1(B_151,u1_struct_0(A_152))
      | ~ l1_orders_2(A_152)
      | ~ v5_orders_2(A_152)
      | ~ v4_orders_2(A_152)
      | ~ v3_orders_2(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_653,plain,(
    ! [B_151,C_154] :
      ( r2_hidden(B_151,k3_orders_2('#skF_2','#skF_5',C_154))
      | ~ r2_hidden(B_151,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_151,C_154)
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_649])).

tff(c_657,plain,(
    ! [B_151,C_154] :
      ( r2_hidden(B_151,k3_orders_2('#skF_2','#skF_5',C_154))
      | ~ r2_hidden(B_151,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_151,C_154)
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_653])).

tff(c_677,plain,(
    ! [B_157,C_158] :
      ( r2_hidden(B_157,k3_orders_2('#skF_2','#skF_5',C_158))
      | ~ r2_hidden(B_157,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_157,C_158)
      | ~ m1_subset_1(C_158,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_157,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_657])).

tff(c_703,plain,(
    ! [A_1,C_158] :
      ( r1_tarski(A_1,k3_orders_2('#skF_2','#skF_5',C_158))
      | ~ r2_hidden('#skF_1'(A_1,k3_orders_2('#skF_2','#skF_5',C_158)),'#skF_5')
      | ~ r2_orders_2('#skF_2','#skF_1'(A_1,k3_orders_2('#skF_2','#skF_5',C_158)),C_158)
      | ~ m1_subset_1(C_158,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_1,k3_orders_2('#skF_2','#skF_5',C_158)),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_677,c_4])).

tff(c_1451,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
    | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_1448,c_703])).

tff(c_1458,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5')
    | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1451])).

tff(c_1459,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1458])).

tff(c_1466,plain,(
    ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1459])).

tff(c_1486,plain,
    ( ~ r1_tarski('#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_1234,c_1466])).

tff(c_1504,plain,(
    r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_53,c_1486])).

tff(c_1506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1504])).

tff(c_1507,plain,(
    ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1459])).

tff(c_1520,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_1273,c_1507])).

tff(c_1529,plain,(
    r1_tarski(k3_orders_2('#skF_2','#skF_5','#skF_3'),k3_orders_2('#skF_2','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1520])).

tff(c_1531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.80  
% 4.64/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.81  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.64/1.81  
% 4.64/1.81  %Foreground sorts:
% 4.64/1.81  
% 4.64/1.81  
% 4.64/1.81  %Background operators:
% 4.64/1.81  
% 4.64/1.81  
% 4.64/1.81  %Foreground operators:
% 4.64/1.81  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.64/1.81  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.64/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.64/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.64/1.81  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.64/1.81  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 4.64/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.64/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.64/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.64/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.64/1.81  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.64/1.81  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.64/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.64/1.81  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.64/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.64/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.64/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.64/1.81  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 4.64/1.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.64/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.64/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.64/1.81  
% 4.74/1.84  tff(f_146, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_orders_2(A, B, C) => r1_tarski(k3_orders_2(A, D, B), k3_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_orders_2)).
% 4.74/1.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.74/1.84  tff(f_70, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 4.74/1.84  tff(f_38, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.74/1.84  tff(f_121, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 4.74/1.84  tff(f_53, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 4.74/1.84  tff(f_95, axiom, (![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((r2_orders_2(A, B, C) & r1_orders_2(A, C, D)) | (r1_orders_2(A, B, C) & r2_orders_2(A, C, D))) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_orders_2)).
% 4.74/1.84  tff(c_28, plain, (~r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.74/1.84  tff(c_36, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.74/1.84  tff(c_48, plain, (![A_62, B_63]: (r2_hidden('#skF_1'(A_62, B_63), A_62) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.74/1.84  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.74/1.84  tff(c_53, plain, (![A_62]: (r1_tarski(A_62, A_62))), inference(resolution, [status(thm)], [c_48, c_4])).
% 4.74/1.84  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.74/1.84  tff(c_44, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.74/1.84  tff(c_42, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.74/1.84  tff(c_40, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.74/1.84  tff(c_38, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.74/1.84  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.74/1.84  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.74/1.84  tff(c_55, plain, (![C_65, B_66, A_67]: (r2_hidden(C_65, B_66) | ~r2_hidden(C_65, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.74/1.84  tff(c_58, plain, (![A_1, B_2, B_66]: (r2_hidden('#skF_1'(A_1, B_2), B_66) | ~r1_tarski(A_1, B_66) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_55])).
% 4.74/1.84  tff(c_115, plain, (![A_88, B_89, C_90]: (m1_subset_1(k3_orders_2(A_88, B_89, C_90), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(C_90, u1_struct_0(A_88)) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_orders_2(A_88) | ~v5_orders_2(A_88) | ~v4_orders_2(A_88) | ~v3_orders_2(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.74/1.84  tff(c_8, plain, (![A_6, C_8, B_7]: (m1_subset_1(A_6, C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.74/1.84  tff(c_210, plain, (![A_100, A_101, B_102, C_103]: (m1_subset_1(A_100, u1_struct_0(A_101)) | ~r2_hidden(A_100, k3_orders_2(A_101, B_102, C_103)) | ~m1_subset_1(C_103, u1_struct_0(A_101)) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_orders_2(A_101) | ~v5_orders_2(A_101) | ~v4_orders_2(A_101) | ~v3_orders_2(A_101) | v2_struct_0(A_101))), inference(resolution, [status(thm)], [c_115, c_8])).
% 4.74/1.84  tff(c_1212, plain, (![A_252, B_250, B_251, C_253, A_249]: (m1_subset_1('#skF_1'(A_252, B_251), u1_struct_0(A_249)) | ~m1_subset_1(C_253, u1_struct_0(A_249)) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_orders_2(A_249) | ~v5_orders_2(A_249) | ~v4_orders_2(A_249) | ~v3_orders_2(A_249) | v2_struct_0(A_249) | ~r1_tarski(A_252, k3_orders_2(A_249, B_250, C_253)) | r1_tarski(A_252, B_251))), inference(resolution, [status(thm)], [c_58, c_210])).
% 4.74/1.84  tff(c_1216, plain, (![A_252, B_251, C_253]: (m1_subset_1('#skF_1'(A_252, B_251), u1_struct_0('#skF_2')) | ~m1_subset_1(C_253, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_252, k3_orders_2('#skF_2', '#skF_5', C_253)) | r1_tarski(A_252, B_251))), inference(resolution, [status(thm)], [c_32, c_1212])).
% 4.74/1.84  tff(c_1220, plain, (![A_252, B_251, C_253]: (m1_subset_1('#skF_1'(A_252, B_251), u1_struct_0('#skF_2')) | ~m1_subset_1(C_253, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(A_252, k3_orders_2('#skF_2', '#skF_5', C_253)) | r1_tarski(A_252, B_251))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_1216])).
% 4.74/1.84  tff(c_1259, plain, (![A_259, B_260, C_261]: (m1_subset_1('#skF_1'(A_259, B_260), u1_struct_0('#skF_2')) | ~m1_subset_1(C_261, u1_struct_0('#skF_2')) | ~r1_tarski(A_259, k3_orders_2('#skF_2', '#skF_5', C_261)) | r1_tarski(A_259, B_260))), inference(negUnitSimplification, [status(thm)], [c_46, c_1220])).
% 4.74/1.84  tff(c_1273, plain, (![C_261, B_260]: (m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_261), B_260), u1_struct_0('#skF_2')) | ~m1_subset_1(C_261, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_261), B_260))), inference(resolution, [status(thm)], [c_53, c_1259])).
% 4.74/1.84  tff(c_1107, plain, (![A_241, B_242, C_243, B_244]: (m1_subset_1('#skF_1'(k3_orders_2(A_241, B_242, C_243), B_244), u1_struct_0(A_241)) | ~m1_subset_1(C_243, u1_struct_0(A_241)) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_orders_2(A_241) | ~v5_orders_2(A_241) | ~v4_orders_2(A_241) | ~v3_orders_2(A_241) | v2_struct_0(A_241) | r1_tarski(k3_orders_2(A_241, B_242, C_243), B_244))), inference(resolution, [status(thm)], [c_6, c_210])).
% 4.74/1.84  tff(c_357, plain, (![B_120, D_121, A_122, C_123]: (r2_hidden(B_120, D_121) | ~r2_hidden(B_120, k3_orders_2(A_122, D_121, C_123)) | ~m1_subset_1(D_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_subset_1(C_123, u1_struct_0(A_122)) | ~m1_subset_1(B_120, u1_struct_0(A_122)) | ~l1_orders_2(A_122) | ~v5_orders_2(A_122) | ~v4_orders_2(A_122) | ~v3_orders_2(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.74/1.84  tff(c_365, plain, (![A_122, D_121, C_123, B_2]: (r2_hidden('#skF_1'(k3_orders_2(A_122, D_121, C_123), B_2), D_121) | ~m1_subset_1(D_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_subset_1(C_123, u1_struct_0(A_122)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_122, D_121, C_123), B_2), u1_struct_0(A_122)) | ~l1_orders_2(A_122) | ~v5_orders_2(A_122) | ~v4_orders_2(A_122) | ~v3_orders_2(A_122) | v2_struct_0(A_122) | r1_tarski(k3_orders_2(A_122, D_121, C_123), B_2))), inference(resolution, [status(thm)], [c_6, c_357])).
% 4.74/1.85  tff(c_1184, plain, (![A_245, B_246, C_247, B_248]: (r2_hidden('#skF_1'(k3_orders_2(A_245, B_246, C_247), B_248), B_246) | ~m1_subset_1(C_247, u1_struct_0(A_245)) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_orders_2(A_245) | ~v5_orders_2(A_245) | ~v4_orders_2(A_245) | ~v3_orders_2(A_245) | v2_struct_0(A_245) | r1_tarski(k3_orders_2(A_245, B_246, C_247), B_248))), inference(resolution, [status(thm)], [c_1107, c_365])).
% 4.74/1.85  tff(c_60, plain, (![A_70, C_71, B_72]: (m1_subset_1(A_70, C_71) | ~m1_subset_1(B_72, k1_zfmisc_1(C_71)) | ~r2_hidden(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.74/1.85  tff(c_63, plain, (![A_70]: (m1_subset_1(A_70, u1_struct_0('#skF_2')) | ~r2_hidden(A_70, '#skF_5'))), inference(resolution, [status(thm)], [c_32, c_60])).
% 4.74/1.85  tff(c_777, plain, (![A_170, D_171, C_172, B_173]: (r2_hidden('#skF_1'(k3_orders_2(A_170, D_171, C_172), B_173), D_171) | ~m1_subset_1(D_171, k1_zfmisc_1(u1_struct_0(A_170))) | ~m1_subset_1(C_172, u1_struct_0(A_170)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_170, D_171, C_172), B_173), u1_struct_0(A_170)) | ~l1_orders_2(A_170) | ~v5_orders_2(A_170) | ~v4_orders_2(A_170) | ~v3_orders_2(A_170) | v2_struct_0(A_170) | r1_tarski(k3_orders_2(A_170, D_171, C_172), B_173))), inference(resolution, [status(thm)], [c_6, c_357])).
% 4.74/1.85  tff(c_780, plain, (![D_171, C_172, B_173]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_171, C_172), B_173), D_171) | ~m1_subset_1(D_171, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_172, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', D_171, C_172), B_173) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_171, C_172), B_173), '#skF_5'))), inference(resolution, [status(thm)], [c_63, c_777])).
% 4.74/1.85  tff(c_783, plain, (![D_171, C_172, B_173]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_171, C_172), B_173), D_171) | ~m1_subset_1(D_171, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_172, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', D_171, C_172), B_173) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_171, C_172), B_173), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_780])).
% 4.74/1.85  tff(c_784, plain, (![D_171, C_172, B_173]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_171, C_172), B_173), D_171) | ~m1_subset_1(D_171, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_172, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', D_171, C_172), B_173) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_171, C_172), B_173), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_46, c_783])).
% 4.74/1.85  tff(c_1187, plain, (![C_247, B_248]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_247), B_248), '#skF_5') | ~m1_subset_1(C_247, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_247), B_248))), inference(resolution, [status(thm)], [c_1184, c_784])).
% 4.74/1.85  tff(c_1205, plain, (![C_247, B_248]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_247), B_248), '#skF_5') | ~m1_subset_1(C_247, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_247), B_248))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_32, c_1187])).
% 4.74/1.85  tff(c_1222, plain, (![C_254, B_255]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_254), B_255), '#skF_5') | ~m1_subset_1(C_254, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_254), B_255))), inference(negUnitSimplification, [status(thm)], [c_46, c_1205])).
% 4.74/1.85  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.74/1.85  tff(c_1234, plain, (![C_254, B_255, B_2]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_254), B_255), B_2) | ~r1_tarski('#skF_5', B_2) | ~m1_subset_1(C_254, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_254), B_255))), inference(resolution, [status(thm)], [c_1222, c_2])).
% 4.74/1.85  tff(c_34, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.74/1.85  tff(c_1289, plain, (![C_265, B_266]: (m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_265), B_266), u1_struct_0('#skF_2')) | ~m1_subset_1(C_265, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_265), B_266))), inference(resolution, [status(thm)], [c_53, c_1259])).
% 4.74/1.85  tff(c_468, plain, (![A_140, B_141, C_142, D_143]: (r2_orders_2(A_140, B_141, C_142) | ~r2_hidden(B_141, k3_orders_2(A_140, D_143, C_142)) | ~m1_subset_1(D_143, k1_zfmisc_1(u1_struct_0(A_140))) | ~m1_subset_1(C_142, u1_struct_0(A_140)) | ~m1_subset_1(B_141, u1_struct_0(A_140)) | ~l1_orders_2(A_140) | ~v5_orders_2(A_140) | ~v4_orders_2(A_140) | ~v3_orders_2(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.74/1.85  tff(c_476, plain, (![A_140, D_143, C_142, B_2]: (r2_orders_2(A_140, '#skF_1'(k3_orders_2(A_140, D_143, C_142), B_2), C_142) | ~m1_subset_1(D_143, k1_zfmisc_1(u1_struct_0(A_140))) | ~m1_subset_1(C_142, u1_struct_0(A_140)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_140, D_143, C_142), B_2), u1_struct_0(A_140)) | ~l1_orders_2(A_140) | ~v5_orders_2(A_140) | ~v4_orders_2(A_140) | ~v3_orders_2(A_140) | v2_struct_0(A_140) | r1_tarski(k3_orders_2(A_140, D_143, C_142), B_2))), inference(resolution, [status(thm)], [c_6, c_468])).
% 4.74/1.85  tff(c_1291, plain, (![C_265, B_266]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_265), B_266), C_265) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_265, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_265), B_266))), inference(resolution, [status(thm)], [c_1289, c_476])).
% 4.74/1.85  tff(c_1318, plain, (![C_265, B_266]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_265), B_266), C_265) | v2_struct_0('#skF_2') | ~m1_subset_1(C_265, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_265), B_266))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_32, c_1291])).
% 4.74/1.85  tff(c_1332, plain, (![C_267, B_268]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_267), B_268), C_267) | ~m1_subset_1(C_267, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_267), B_268))), inference(negUnitSimplification, [status(thm)], [c_46, c_1318])).
% 4.74/1.85  tff(c_30, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.74/1.85  tff(c_78, plain, (![A_81, B_82, C_83]: (r1_orders_2(A_81, B_82, C_83) | ~r2_orders_2(A_81, B_82, C_83) | ~m1_subset_1(C_83, u1_struct_0(A_81)) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l1_orders_2(A_81))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.74/1.85  tff(c_80, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_30, c_78])).
% 4.74/1.85  tff(c_83, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_80])).
% 4.74/1.85  tff(c_219, plain, (![A_104, C_105, D_106, B_107]: (~r1_orders_2(A_104, C_105, D_106) | ~r2_orders_2(A_104, B_107, C_105) | r2_orders_2(A_104, B_107, D_106) | ~m1_subset_1(D_106, u1_struct_0(A_104)) | ~m1_subset_1(C_105, u1_struct_0(A_104)) | ~m1_subset_1(B_107, u1_struct_0(A_104)) | ~l1_orders_2(A_104) | ~v5_orders_2(A_104) | ~v4_orders_2(A_104))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.74/1.85  tff(c_221, plain, (![B_107]: (~r2_orders_2('#skF_2', B_107, '#skF_3') | r2_orders_2('#skF_2', B_107, '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_107, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_83, c_219])).
% 4.74/1.85  tff(c_287, plain, (![B_114]: (~r2_orders_2('#skF_2', B_114, '#skF_3') | r2_orders_2('#skF_2', B_114, '#skF_4') | ~m1_subset_1(B_114, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_221])).
% 4.74/1.85  tff(c_297, plain, (![A_70]: (~r2_orders_2('#skF_2', A_70, '#skF_3') | r2_orders_2('#skF_2', A_70, '#skF_4') | ~r2_hidden(A_70, '#skF_5'))), inference(resolution, [status(thm)], [c_63, c_287])).
% 4.74/1.85  tff(c_1339, plain, (![B_268]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), B_268), '#skF_4') | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), B_268), '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), B_268))), inference(resolution, [status(thm)], [c_1332, c_297])).
% 4.74/1.85  tff(c_1448, plain, (![B_278]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), B_278), '#skF_4') | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), B_278), '#skF_5') | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), B_278))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1339])).
% 4.74/1.85  tff(c_649, plain, (![B_151, A_152, D_153, C_154]: (r2_hidden(B_151, k3_orders_2(A_152, D_153, C_154)) | ~r2_hidden(B_151, D_153) | ~r2_orders_2(A_152, B_151, C_154) | ~m1_subset_1(D_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~m1_subset_1(C_154, u1_struct_0(A_152)) | ~m1_subset_1(B_151, u1_struct_0(A_152)) | ~l1_orders_2(A_152) | ~v5_orders_2(A_152) | ~v4_orders_2(A_152) | ~v3_orders_2(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.74/1.85  tff(c_653, plain, (![B_151, C_154]: (r2_hidden(B_151, k3_orders_2('#skF_2', '#skF_5', C_154)) | ~r2_hidden(B_151, '#skF_5') | ~r2_orders_2('#skF_2', B_151, C_154) | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_151, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_649])).
% 4.74/1.85  tff(c_657, plain, (![B_151, C_154]: (r2_hidden(B_151, k3_orders_2('#skF_2', '#skF_5', C_154)) | ~r2_hidden(B_151, '#skF_5') | ~r2_orders_2('#skF_2', B_151, C_154) | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~m1_subset_1(B_151, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_653])).
% 4.74/1.85  tff(c_677, plain, (![B_157, C_158]: (r2_hidden(B_157, k3_orders_2('#skF_2', '#skF_5', C_158)) | ~r2_hidden(B_157, '#skF_5') | ~r2_orders_2('#skF_2', B_157, C_158) | ~m1_subset_1(C_158, u1_struct_0('#skF_2')) | ~m1_subset_1(B_157, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_657])).
% 4.74/1.85  tff(c_703, plain, (![A_1, C_158]: (r1_tarski(A_1, k3_orders_2('#skF_2', '#skF_5', C_158)) | ~r2_hidden('#skF_1'(A_1, k3_orders_2('#skF_2', '#skF_5', C_158)), '#skF_5') | ~r2_orders_2('#skF_2', '#skF_1'(A_1, k3_orders_2('#skF_2', '#skF_5', C_158)), C_158) | ~m1_subset_1(C_158, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_1, k3_orders_2('#skF_2', '#skF_5', C_158)), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_677, c_4])).
% 4.74/1.85  tff(c_1451, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_1448, c_703])).
% 4.74/1.85  tff(c_1458, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5') | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1451])).
% 4.74/1.85  tff(c_1459, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_28, c_1458])).
% 4.74/1.85  tff(c_1466, plain, (~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), '#skF_5')), inference(splitLeft, [status(thm)], [c_1459])).
% 4.74/1.85  tff(c_1486, plain, (~r1_tarski('#skF_5', '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_1234, c_1466])).
% 4.74/1.85  tff(c_1504, plain, (r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_53, c_1486])).
% 4.74/1.85  tff(c_1506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_1504])).
% 4.74/1.85  tff(c_1507, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1459])).
% 4.74/1.85  tff(c_1520, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_1273, c_1507])).
% 4.74/1.85  tff(c_1529, plain, (r1_tarski(k3_orders_2('#skF_2', '#skF_5', '#skF_3'), k3_orders_2('#skF_2', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1520])).
% 4.74/1.85  tff(c_1531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_1529])).
% 4.74/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.85  
% 4.74/1.85  Inference rules
% 4.74/1.85  ----------------------
% 4.74/1.85  #Ref     : 0
% 4.74/1.85  #Sup     : 309
% 4.74/1.85  #Fact    : 0
% 4.74/1.85  #Define  : 0
% 4.74/1.85  #Split   : 4
% 4.74/1.85  #Chain   : 0
% 4.74/1.85  #Close   : 0
% 4.74/1.85  
% 4.74/1.85  Ordering : KBO
% 4.74/1.85  
% 4.74/1.85  Simplification rules
% 4.74/1.85  ----------------------
% 4.74/1.85  #Subsume      : 113
% 4.74/1.85  #Demod        : 268
% 4.74/1.85  #Tautology    : 42
% 4.74/1.85  #SimpNegUnit  : 25
% 4.74/1.85  #BackRed      : 0
% 4.74/1.85  
% 4.74/1.85  #Partial instantiations: 0
% 4.74/1.85  #Strategies tried      : 1
% 4.74/1.85  
% 4.74/1.85  Timing (in seconds)
% 4.74/1.85  ----------------------
% 4.74/1.85  Preprocessing        : 0.32
% 4.74/1.85  Parsing              : 0.18
% 4.74/1.85  CNF conversion       : 0.03
% 4.74/1.85  Main loop            : 0.73
% 4.74/1.85  Inferencing          : 0.26
% 4.74/1.85  Reduction            : 0.20
% 4.74/1.85  Demodulation         : 0.13
% 4.74/1.85  BG Simplification    : 0.03
% 4.74/1.85  Subsumption          : 0.21
% 4.74/1.85  Abstraction          : 0.03
% 4.74/1.85  MUC search           : 0.00
% 4.74/1.85  Cooper               : 0.00
% 4.74/1.85  Total                : 1.12
% 4.74/1.85  Index Insertion      : 0.00
% 4.74/1.85  Index Deletion       : 0.00
% 4.74/1.85  Index Matching       : 0.00
% 4.74/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
