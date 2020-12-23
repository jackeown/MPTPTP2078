%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:22 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 641 expanded)
%              Number of leaves         :   22 ( 239 expanded)
%              Depth                    :   11
%              Number of atoms          :  698 (3715 expanded)
%              Number of equality atoms :    7 (  30 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v3_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( ? [D] :
                      ( v6_orders_2(D,A)
                      & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                      & r2_hidden(B,D)
                      & r2_hidden(C,D) )
                <=> ( r2_orders_2(A,B,C)
                  <=> ~ r1_orders_2(A,C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_orders_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ~ ( ? [D] :
                        ( v6_orders_2(D,A)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(B,D)
                        & r2_hidden(C,D) )
                    & ~ r1_orders_2(A,B,C)
                    & ~ r1_orders_2(A,C,B) )
                & ~ ( ( r1_orders_2(A,B,C)
                      | r1_orders_2(A,C,B) )
                    & ! [D] :
                        ( ( v6_orders_2(D,A)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                       => ~ ( r2_hidden(B,D)
                            & r2_hidden(C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_36,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_72,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_86,plain,(
    ~ r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_841,plain,(
    ! [A_249,B_250,C_251] :
      ( r2_orders_2(A_249,B_250,C_251)
      | C_251 = B_250
      | ~ r1_orders_2(A_249,B_250,C_251)
      | ~ m1_subset_1(C_251,u1_struct_0(A_249))
      | ~ m1_subset_1(B_250,u1_struct_0(A_249))
      | ~ l1_orders_2(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_843,plain,(
    ! [B_250] :
      ( r2_orders_2('#skF_2',B_250,'#skF_4')
      | B_250 = '#skF_4'
      | ~ r1_orders_2('#skF_2',B_250,'#skF_4')
      | ~ m1_subset_1(B_250,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_841])).

tff(c_852,plain,(
    ! [B_252] :
      ( r2_orders_2('#skF_2',B_252,'#skF_4')
      | B_252 = '#skF_4'
      | ~ r1_orders_2('#skF_2',B_252,'#skF_4')
      | ~ m1_subset_1(B_252,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_843])).

tff(c_858,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_852])).

tff(c_863,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_858])).

tff(c_864,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_863])).

tff(c_60,plain,
    ( v6_orders_2('#skF_5','#skF_2')
    | r2_orders_2('#skF_2','#skF_3','#skF_4')
    | r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_87,plain,
    ( v6_orders_2('#skF_5','#skF_2')
    | r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_60])).

tff(c_88,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_12,plain,(
    ! [A_15,C_33,B_27] :
      ( ~ r1_orders_2(A_15,C_33,B_27)
      | r2_hidden(C_33,'#skF_1'(A_15,B_27,C_33))
      | ~ m1_subset_1(C_33,u1_struct_0(A_15))
      | ~ m1_subset_1(B_27,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15)
      | ~ v3_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16,plain,(
    ! [A_15,C_33,B_27] :
      ( ~ r1_orders_2(A_15,C_33,B_27)
      | r2_hidden(B_27,'#skF_1'(A_15,B_27,C_33))
      | ~ m1_subset_1(C_33,u1_struct_0(A_15))
      | ~ m1_subset_1(B_27,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15)
      | ~ v3_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    ! [A_15,C_33,B_27] :
      ( ~ r1_orders_2(A_15,C_33,B_27)
      | v6_orders_2('#skF_1'(A_15,B_27,C_33),A_15)
      | ~ m1_subset_1(C_33,u1_struct_0(A_15))
      | ~ m1_subset_1(B_27,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15)
      | ~ v3_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_536,plain,(
    ! [A_181,C_182,B_183] :
      ( ~ r1_orders_2(A_181,C_182,B_183)
      | m1_subset_1('#skF_1'(A_181,B_183,C_182),k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ m1_subset_1(C_182,u1_struct_0(A_181))
      | ~ m1_subset_1(B_183,u1_struct_0(A_181))
      | ~ l1_orders_2(A_181)
      | ~ v3_orders_2(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    ! [D_55] :
      ( v6_orders_2('#skF_5','#skF_2')
      | ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_456,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_540,plain,(
    ! [B_183,C_182] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_183,C_182))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_183,C_182))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_183,C_182),'#skF_2')
      | ~ r1_orders_2('#skF_2',C_182,B_183)
      | ~ m1_subset_1(C_182,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_183,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_536,c_456])).

tff(c_552,plain,(
    ! [B_187,C_188] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_187,C_188))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_187,C_188))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_187,C_188),'#skF_2')
      | ~ r1_orders_2('#skF_2',C_188,B_187)
      | ~ m1_subset_1(C_188,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_187,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_540])).

tff(c_560,plain,(
    ! [B_27,C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,C_33))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_27,C_33))
      | ~ r1_orders_2('#skF_2',C_33,B_27)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_552])).

tff(c_586,plain,(
    ! [B_193,C_194] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_193,C_194))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_193,C_194))
      | ~ r1_orders_2('#skF_2',C_194,B_193)
      | ~ m1_subset_1(C_194,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_193,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_560])).

tff(c_598,plain,(
    ! [C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_33))
      | ~ r1_orders_2('#skF_2',C_33,'#skF_3')
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_586])).

tff(c_630,plain,(
    ! [C_196] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_196))
      | ~ r1_orders_2('#skF_2',C_196,'#skF_3')
      | ~ m1_subset_1(C_196,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_598])).

tff(c_634,plain,
    ( ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_630])).

tff(c_642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_28,c_88,c_634])).

tff(c_643,plain,(
    v6_orders_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_18,plain,(
    ! [A_15,B_27,C_33] :
      ( ~ r1_orders_2(A_15,B_27,C_33)
      | r2_hidden(B_27,'#skF_1'(A_15,B_27,C_33))
      | ~ m1_subset_1(C_33,u1_struct_0(A_15))
      | ~ m1_subset_1(B_27,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15)
      | ~ v3_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_14,plain,(
    ! [A_15,B_27,C_33] :
      ( ~ r1_orders_2(A_15,B_27,C_33)
      | r2_hidden(C_33,'#skF_1'(A_15,B_27,C_33))
      | ~ m1_subset_1(C_33,u1_struct_0(A_15))
      | ~ m1_subset_1(B_27,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15)
      | ~ v3_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    ! [A_15,B_27,C_33] :
      ( ~ r1_orders_2(A_15,B_27,C_33)
      | v6_orders_2('#skF_1'(A_15,B_27,C_33),A_15)
      | ~ m1_subset_1(C_33,u1_struct_0(A_15))
      | ~ m1_subset_1(B_27,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15)
      | ~ v3_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_352,plain,(
    ! [A_137,B_138,C_139] :
      ( ~ r1_orders_2(A_137,B_138,C_139)
      | m1_subset_1('#skF_1'(A_137,B_138,C_139),k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ m1_subset_1(C_139,u1_struct_0(A_137))
      | ~ m1_subset_1(B_138,u1_struct_0(A_137))
      | ~ l1_orders_2(A_137)
      | ~ v3_orders_2(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    ! [D_55] :
      ( r2_hidden('#skF_3','#skF_5')
      | ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_276,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_356,plain,(
    ! [B_138,C_139] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_138,C_139))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_138,C_139))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_138,C_139),'#skF_2')
      | ~ r1_orders_2('#skF_2',B_138,C_139)
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_352,c_276])).

tff(c_368,plain,(
    ! [B_143,C_144] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_143,C_144))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_143,C_144))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_143,C_144),'#skF_2')
      | ~ r1_orders_2('#skF_2',B_143,C_144)
      | ~ m1_subset_1(C_144,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_143,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_356])).

tff(c_372,plain,(
    ! [B_27,C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,C_33))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_27,C_33))
      | ~ r1_orders_2('#skF_2',B_27,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_368])).

tff(c_398,plain,(
    ! [B_147,C_148] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_147,C_148))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_147,C_148))
      | ~ r1_orders_2('#skF_2',B_147,C_148)
      | ~ m1_subset_1(C_148,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_372])).

tff(c_414,plain,(
    ! [B_27] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,'#skF_3'))
      | ~ r1_orders_2('#skF_2',B_27,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_398])).

tff(c_442,plain,(
    ! [B_150] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_150,'#skF_3'))
      | ~ r1_orders_2('#skF_2',B_150,'#skF_3')
      | ~ m1_subset_1(B_150,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_414])).

tff(c_446,plain,
    ( ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_442])).

tff(c_454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_28,c_30,c_88,c_446])).

tff(c_455,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_174,plain,(
    ! [A_88,B_89,C_90] :
      ( ~ r1_orders_2(A_88,B_89,C_90)
      | m1_subset_1('#skF_1'(A_88,B_89,C_90),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(C_90,u1_struct_0(A_88))
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l1_orders_2(A_88)
      | ~ v3_orders_2(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    ! [D_55] :
      ( r2_hidden('#skF_4','#skF_5')
      | ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_99,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_178,plain,(
    ! [B_89,C_90] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_89,C_90))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_89,C_90))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_89,C_90),'#skF_2')
      | ~ r1_orders_2('#skF_2',B_89,C_90)
      | ~ m1_subset_1(C_90,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_89,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_174,c_99])).

tff(c_190,plain,(
    ! [B_94,C_95] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_94,C_95))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_94,C_95))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_94,C_95),'#skF_2')
      | ~ r1_orders_2('#skF_2',B_94,C_95)
      | ~ m1_subset_1(C_95,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_178])).

tff(c_198,plain,(
    ! [B_27,C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,C_33))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_27,C_33))
      | ~ r1_orders_2('#skF_2',B_27,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_190])).

tff(c_218,plain,(
    ! [B_100,C_101] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_100,C_101))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_100,C_101))
      | ~ r1_orders_2('#skF_2',B_100,C_101)
      | ~ m1_subset_1(C_101,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_198])).

tff(c_230,plain,(
    ! [B_27] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,'#skF_3'))
      | ~ r1_orders_2('#skF_2',B_27,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_218])).

tff(c_262,plain,(
    ! [B_103] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_103,'#skF_3'))
      | ~ r1_orders_2('#skF_2',B_103,'#skF_3')
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_230])).

tff(c_266,plain,
    ( ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_262])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_28,c_30,c_88,c_266])).

tff(c_275,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_721,plain,(
    ! [A_227,B_228,C_229] :
      ( ~ r1_orders_2(A_227,B_228,C_229)
      | m1_subset_1('#skF_1'(A_227,B_228,C_229),k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ m1_subset_1(C_229,u1_struct_0(A_227))
      | ~ m1_subset_1(B_228,u1_struct_0(A_227))
      | ~ l1_orders_2(A_227)
      | ~ v3_orders_2(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42,plain,(
    ! [D_55] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_644,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_725,plain,(
    ! [B_228,C_229] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_228,C_229))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_228,C_229))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_228,C_229),'#skF_2')
      | ~ r1_orders_2('#skF_2',B_228,C_229)
      | ~ m1_subset_1(C_229,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_228,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_721,c_644])).

tff(c_756,plain,(
    ! [B_237,C_238] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_237,C_238))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_237,C_238))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_237,C_238),'#skF_2')
      | ~ r1_orders_2('#skF_2',B_237,C_238)
      | ~ m1_subset_1(C_238,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_237,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_725])).

tff(c_760,plain,(
    ! [B_27,C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,C_33))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_27,C_33))
      | ~ r1_orders_2('#skF_2',B_27,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_756])).

tff(c_771,plain,(
    ! [B_239,C_240] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_239,C_240))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_239,C_240))
      | ~ r1_orders_2('#skF_2',B_239,C_240)
      | ~ m1_subset_1(C_240,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_239,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_760])).

tff(c_783,plain,(
    ! [B_27] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,'#skF_3'))
      | ~ r1_orders_2('#skF_2',B_27,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_771])).

tff(c_800,plain,(
    ! [B_241] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_241,'#skF_3'))
      | ~ r1_orders_2('#skF_2',B_241,'#skF_3')
      | ~ m1_subset_1(B_241,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_783])).

tff(c_808,plain,
    ( ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_800])).

tff(c_815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_28,c_30,c_88,c_808])).

tff(c_816,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_52,plain,(
    ! [D_55] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_4')
      | ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
      | ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_818,plain,(
    ! [D_55] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_52])).

tff(c_819,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_818])).

tff(c_823,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_3','#skF_5')
    | ~ v6_orders_2('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_816,c_819])).

tff(c_827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_455,c_275,c_823])).

tff(c_829,plain,(
    ~ r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_56,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_orders_2('#skF_2','#skF_3','#skF_4')
    | r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_830,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_829,c_86,c_56])).

tff(c_828,plain,(
    v6_orders_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_58,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | r2_orders_2('#skF_2','#skF_3','#skF_4')
    | r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_833,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_829,c_86,c_58])).

tff(c_54,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_orders_2('#skF_2','#skF_3','#skF_4')
    | r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_832,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_829,c_86,c_54])).

tff(c_885,plain,(
    ! [A_278,C_279,B_280,D_281] :
      ( r1_orders_2(A_278,C_279,B_280)
      | r1_orders_2(A_278,B_280,C_279)
      | ~ r2_hidden(C_279,D_281)
      | ~ r2_hidden(B_280,D_281)
      | ~ m1_subset_1(D_281,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ v6_orders_2(D_281,A_278)
      | ~ m1_subset_1(C_279,u1_struct_0(A_278))
      | ~ m1_subset_1(B_280,u1_struct_0(A_278))
      | ~ l1_orders_2(A_278)
      | ~ v3_orders_2(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_904,plain,(
    ! [A_282,B_283] :
      ( r1_orders_2(A_282,'#skF_4',B_283)
      | r1_orders_2(A_282,B_283,'#skF_4')
      | ~ r2_hidden(B_283,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ v6_orders_2('#skF_5',A_282)
      | ~ m1_subset_1('#skF_4',u1_struct_0(A_282))
      | ~ m1_subset_1(B_283,u1_struct_0(A_282))
      | ~ l1_orders_2(A_282)
      | ~ v3_orders_2(A_282) ) ),
    inference(resolution,[status(thm)],[c_832,c_885])).

tff(c_906,plain,(
    ! [B_283] :
      ( r1_orders_2('#skF_2','#skF_4',B_283)
      | r1_orders_2('#skF_2',B_283,'#skF_4')
      | ~ r2_hidden(B_283,'#skF_5')
      | ~ v6_orders_2('#skF_5','#skF_2')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_283,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_833,c_904])).

tff(c_910,plain,(
    ! [B_284] :
      ( r1_orders_2('#skF_2','#skF_4',B_284)
      | r1_orders_2('#skF_2',B_284,'#skF_4')
      | ~ r2_hidden(B_284,'#skF_5')
      | ~ m1_subset_1(B_284,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_28,c_828,c_906])).

tff(c_916,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_3')
    | r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_910])).

tff(c_922,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_3')
    | r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_916])).

tff(c_924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_864,c_829,c_922])).

tff(c_925,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_863])).

tff(c_926,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_863])).

tff(c_937,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_926])).

tff(c_928,plain,(
    ~ r1_orders_2('#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_829])).

tff(c_940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_937,c_928])).

tff(c_942,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1267,plain,(
    ! [A_378,B_379,C_380] :
      ( r1_orders_2(A_378,B_379,C_380)
      | ~ r2_orders_2(A_378,B_379,C_380)
      | ~ m1_subset_1(C_380,u1_struct_0(A_378))
      | ~ m1_subset_1(B_379,u1_struct_0(A_378))
      | ~ l1_orders_2(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1269,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_942,c_1267])).

tff(c_1272,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_1269])).

tff(c_1322,plain,(
    ! [A_407,C_408,B_409] :
      ( ~ r1_orders_2(A_407,C_408,B_409)
      | m1_subset_1('#skF_1'(A_407,B_409,C_408),k1_zfmisc_1(u1_struct_0(A_407)))
      | ~ m1_subset_1(C_408,u1_struct_0(A_407))
      | ~ m1_subset_1(B_409,u1_struct_0(A_407))
      | ~ l1_orders_2(A_407)
      | ~ v3_orders_2(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1265,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_1326,plain,(
    ! [B_409,C_408] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_409,C_408))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_409,C_408))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_409,C_408),'#skF_2')
      | ~ r1_orders_2('#skF_2',C_408,B_409)
      | ~ m1_subset_1(C_408,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_409,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1322,c_1265])).

tff(c_1338,plain,(
    ! [B_413,C_414] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_413,C_414))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_413,C_414))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_413,C_414),'#skF_2')
      | ~ r1_orders_2('#skF_2',C_414,B_413)
      | ~ m1_subset_1(C_414,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_413,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1326])).

tff(c_1342,plain,(
    ! [B_27,C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,C_33))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_27,C_33))
      | ~ r1_orders_2('#skF_2',C_33,B_27)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_1338])).

tff(c_1368,plain,(
    ! [B_417,C_418] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_417,C_418))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_417,C_418))
      | ~ r1_orders_2('#skF_2',C_418,B_417)
      | ~ m1_subset_1(C_418,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_417,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1342])).

tff(c_1372,plain,(
    ! [B_27] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,'#skF_3'))
      | ~ r1_orders_2('#skF_2','#skF_3',B_27)
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_1368])).

tff(c_1397,plain,(
    ! [B_419] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_419,'#skF_3'))
      | ~ r1_orders_2('#skF_2','#skF_3',B_419)
      | ~ m1_subset_1(B_419,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_1372])).

tff(c_1401,plain,
    ( ~ r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_1397])).

tff(c_1409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_28,c_30,c_1272,c_1401])).

tff(c_1410,plain,(
    v6_orders_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1120,plain,(
    ! [A_333,B_334,C_335] :
      ( r1_orders_2(A_333,B_334,C_335)
      | ~ r2_orders_2(A_333,B_334,C_335)
      | ~ m1_subset_1(C_335,u1_struct_0(A_333))
      | ~ m1_subset_1(B_334,u1_struct_0(A_333))
      | ~ l1_orders_2(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1122,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_942,c_1120])).

tff(c_1125,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_1122])).

tff(c_1175,plain,(
    ! [A_362,C_363,B_364] :
      ( ~ r1_orders_2(A_362,C_363,B_364)
      | m1_subset_1('#skF_1'(A_362,B_364,C_363),k1_zfmisc_1(u1_struct_0(A_362)))
      | ~ m1_subset_1(C_363,u1_struct_0(A_362))
      | ~ m1_subset_1(B_364,u1_struct_0(A_362))
      | ~ l1_orders_2(A_362)
      | ~ v3_orders_2(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1118,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_1179,plain,(
    ! [B_364,C_363] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_364,C_363))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_364,C_363))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_364,C_363),'#skF_2')
      | ~ r1_orders_2('#skF_2',C_363,B_364)
      | ~ m1_subset_1(C_363,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_364,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1175,c_1118])).

tff(c_1191,plain,(
    ! [B_368,C_369] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_368,C_369))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_368,C_369))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_368,C_369),'#skF_2')
      | ~ r1_orders_2('#skF_2',C_369,B_368)
      | ~ m1_subset_1(C_369,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_368,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1179])).

tff(c_1199,plain,(
    ! [B_27,C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,C_33))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_27,C_33))
      | ~ r1_orders_2('#skF_2',C_33,B_27)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_1191])).

tff(c_1222,plain,(
    ! [B_374,C_375] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_374,C_375))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_374,C_375))
      | ~ r1_orders_2('#skF_2',C_375,B_374)
      | ~ m1_subset_1(C_375,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_374,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1199])).

tff(c_1226,plain,(
    ! [B_27] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,'#skF_3'))
      | ~ r1_orders_2('#skF_2','#skF_3',B_27)
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_1222])).

tff(c_1251,plain,(
    ! [B_376] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_376,'#skF_3'))
      | ~ r1_orders_2('#skF_2','#skF_3',B_376)
      | ~ m1_subset_1(B_376,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_1226])).

tff(c_1255,plain,
    ( ~ r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_1251])).

tff(c_1263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_28,c_30,c_1125,c_1255])).

tff(c_1264,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_959,plain,(
    ! [A_289,B_290,C_291] :
      ( r1_orders_2(A_289,B_290,C_291)
      | ~ r2_orders_2(A_289,B_290,C_291)
      | ~ m1_subset_1(C_291,u1_struct_0(A_289))
      | ~ m1_subset_1(B_290,u1_struct_0(A_289))
      | ~ l1_orders_2(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_961,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_942,c_959])).

tff(c_964,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_961])).

tff(c_1014,plain,(
    ! [A_318,C_319,B_320] :
      ( ~ r1_orders_2(A_318,C_319,B_320)
      | m1_subset_1('#skF_1'(A_318,B_320,C_319),k1_zfmisc_1(u1_struct_0(A_318)))
      | ~ m1_subset_1(C_319,u1_struct_0(A_318))
      | ~ m1_subset_1(B_320,u1_struct_0(A_318))
      | ~ l1_orders_2(A_318)
      | ~ v3_orders_2(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_957,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_1018,plain,(
    ! [B_320,C_319] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_320,C_319))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_320,C_319))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_320,C_319),'#skF_2')
      | ~ r1_orders_2('#skF_2',C_319,B_320)
      | ~ m1_subset_1(C_319,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_320,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1014,c_957])).

tff(c_1030,plain,(
    ! [B_324,C_325] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_324,C_325))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_324,C_325))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_324,C_325),'#skF_2')
      | ~ r1_orders_2('#skF_2',C_325,B_324)
      | ~ m1_subset_1(C_325,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_324,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1018])).

tff(c_1034,plain,(
    ! [B_27,C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,C_33))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_27,C_33))
      | ~ r1_orders_2('#skF_2',C_33,B_27)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_1030])).

tff(c_1060,plain,(
    ! [B_328,C_329] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_328,C_329))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_328,C_329))
      | ~ r1_orders_2('#skF_2',C_329,B_328)
      | ~ m1_subset_1(C_329,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_328,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1034])).

tff(c_1068,plain,(
    ! [B_27] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,'#skF_3'))
      | ~ r1_orders_2('#skF_2','#skF_3',B_27)
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_1060])).

tff(c_1104,plain,(
    ! [B_331] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_331,'#skF_3'))
      | ~ r1_orders_2('#skF_2','#skF_3',B_331)
      | ~ m1_subset_1(B_331,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_1068])).

tff(c_1108,plain,
    ( ~ r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_1104])).

tff(c_1116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_28,c_30,c_964,c_1108])).

tff(c_1117,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1411,plain,(
    ! [A_420,B_421,C_422] :
      ( r1_orders_2(A_420,B_421,C_422)
      | ~ r2_orders_2(A_420,B_421,C_422)
      | ~ m1_subset_1(C_422,u1_struct_0(A_420))
      | ~ m1_subset_1(B_421,u1_struct_0(A_420))
      | ~ l1_orders_2(A_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1413,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_942,c_1411])).

tff(c_1416,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_1413])).

tff(c_1468,plain,(
    ! [A_450,C_451,B_452] :
      ( ~ r1_orders_2(A_450,C_451,B_452)
      | m1_subset_1('#skF_1'(A_450,B_452,C_451),k1_zfmisc_1(u1_struct_0(A_450)))
      | ~ m1_subset_1(C_451,u1_struct_0(A_450))
      | ~ m1_subset_1(B_452,u1_struct_0(A_450))
      | ~ l1_orders_2(A_450)
      | ~ v3_orders_2(A_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1417,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_1472,plain,(
    ! [B_452,C_451] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_452,C_451))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_452,C_451))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_452,C_451),'#skF_2')
      | ~ r1_orders_2('#skF_2',C_451,B_452)
      | ~ m1_subset_1(C_451,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_452,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1468,c_1417])).

tff(c_1484,plain,(
    ! [B_456,C_457] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_456,C_457))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_456,C_457))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_456,C_457),'#skF_2')
      | ~ r1_orders_2('#skF_2',C_457,B_456)
      | ~ m1_subset_1(C_457,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_456,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1472])).

tff(c_1488,plain,(
    ! [B_27,C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,C_33))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_27,C_33))
      | ~ r1_orders_2('#skF_2',C_33,B_27)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_1484])).

tff(c_1499,plain,(
    ! [B_458,C_459] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_458,C_459))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_458,C_459))
      | ~ r1_orders_2('#skF_2',C_459,B_458)
      | ~ m1_subset_1(C_459,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_458,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1488])).

tff(c_1503,plain,(
    ! [B_27] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,'#skF_3'))
      | ~ r1_orders_2('#skF_2','#skF_3',B_27)
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_1499])).

tff(c_1528,plain,(
    ! [B_460] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_460,'#skF_3'))
      | ~ r1_orders_2('#skF_2','#skF_3',B_460)
      | ~ m1_subset_1(B_460,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_1503])).

tff(c_1532,plain,
    ( ~ r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_1528])).

tff(c_1540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_28,c_30,c_1416,c_1532])).

tff(c_1541,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_941,plain,
    ( ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_943,plain,(
    ~ r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_941])).

tff(c_46,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_2','#skF_4','#skF_3')
      | ~ r2_orders_2('#skF_2','#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1582,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_2','#skF_4','#skF_3')
      | ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_46])).

tff(c_1584,plain,(
    ! [D_469] :
      ( ~ r2_hidden('#skF_4',D_469)
      | ~ r2_hidden('#skF_3',D_469)
      | ~ m1_subset_1(D_469,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_469,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_943,c_1582])).

tff(c_1587,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_3','#skF_5')
    | ~ v6_orders_2('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_1541,c_1584])).

tff(c_1591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_1264,c_1117,c_1587])).

tff(c_1593,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_941])).

tff(c_1678,plain,(
    ! [A_478,C_479,B_480] :
      ( ~ r2_orders_2(A_478,C_479,B_480)
      | ~ r1_orders_2(A_478,B_480,C_479)
      | ~ m1_subset_1(C_479,u1_struct_0(A_478))
      | ~ m1_subset_1(B_480,u1_struct_0(A_478))
      | ~ l1_orders_2(A_478)
      | ~ v5_orders_2(A_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1680,plain,
    ( ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_942,c_1678])).

tff(c_1684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_30,c_1593,c_1680])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:42:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.90  
% 4.32/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.90  %$ r2_orders_2 > r1_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v3_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.32/1.90  
% 4.32/1.90  %Foreground sorts:
% 4.32/1.90  
% 4.32/1.90  
% 4.32/1.90  %Background operators:
% 4.32/1.90  
% 4.32/1.90  
% 4.32/1.90  %Foreground operators:
% 4.32/1.90  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.32/1.90  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.32/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.32/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.32/1.90  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.32/1.90  tff('#skF_5', type, '#skF_5': $i).
% 4.32/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.32/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.32/1.90  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.32/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.32/1.90  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.32/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.32/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.32/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.32/1.90  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 4.32/1.90  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 4.32/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.32/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.32/1.90  
% 4.66/1.94  tff(f_123, negated_conjecture, ~(![A]: (((v3_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((?[D]: (((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) & r2_hidden(B, D)) & r2_hidden(C, D))) <=> (r2_orders_2(A, B, C) <=> ~r1_orders_2(A, C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_orders_2)).
% 4.66/1.94  tff(f_40, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 4.66/1.94  tff(f_96, axiom, (![A]: ((v3_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~(((?[D]: (((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) & r2_hidden(B, D)) & r2_hidden(C, D))) & ~r1_orders_2(A, B, C)) & ~r1_orders_2(A, C, B)) & ~((r1_orders_2(A, B, C) | r1_orders_2(A, C, B)) & (![D]: ((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~(r2_hidden(B, D) & r2_hidden(C, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_orders_2)).
% 4.66/1.94  tff(f_55, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_orders_2)).
% 4.66/1.94  tff(c_34, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.94  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.94  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.94  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.94  tff(c_36, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.94  tff(c_72, plain, (r2_hidden('#skF_3', '#skF_5') | ~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.94  tff(c_86, plain, (~r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_72])).
% 4.66/1.94  tff(c_841, plain, (![A_249, B_250, C_251]: (r2_orders_2(A_249, B_250, C_251) | C_251=B_250 | ~r1_orders_2(A_249, B_250, C_251) | ~m1_subset_1(C_251, u1_struct_0(A_249)) | ~m1_subset_1(B_250, u1_struct_0(A_249)) | ~l1_orders_2(A_249))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.66/1.94  tff(c_843, plain, (![B_250]: (r2_orders_2('#skF_2', B_250, '#skF_4') | B_250='#skF_4' | ~r1_orders_2('#skF_2', B_250, '#skF_4') | ~m1_subset_1(B_250, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_841])).
% 4.66/1.94  tff(c_852, plain, (![B_252]: (r2_orders_2('#skF_2', B_252, '#skF_4') | B_252='#skF_4' | ~r1_orders_2('#skF_2', B_252, '#skF_4') | ~m1_subset_1(B_252, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_843])).
% 4.66/1.94  tff(c_858, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4') | '#skF_3'='#skF_4' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_852])).
% 4.66/1.94  tff(c_863, plain, ('#skF_3'='#skF_4' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_86, c_858])).
% 4.66/1.94  tff(c_864, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_863])).
% 4.66/1.94  tff(c_60, plain, (v6_orders_2('#skF_5', '#skF_2') | r2_orders_2('#skF_2', '#skF_3', '#skF_4') | r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.94  tff(c_87, plain, (v6_orders_2('#skF_5', '#skF_2') | r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_86, c_60])).
% 4.66/1.94  tff(c_88, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_87])).
% 4.66/1.94  tff(c_12, plain, (![A_15, C_33, B_27]: (~r1_orders_2(A_15, C_33, B_27) | r2_hidden(C_33, '#skF_1'(A_15, B_27, C_33)) | ~m1_subset_1(C_33, u1_struct_0(A_15)) | ~m1_subset_1(B_27, u1_struct_0(A_15)) | ~l1_orders_2(A_15) | ~v3_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.94  tff(c_16, plain, (![A_15, C_33, B_27]: (~r1_orders_2(A_15, C_33, B_27) | r2_hidden(B_27, '#skF_1'(A_15, B_27, C_33)) | ~m1_subset_1(C_33, u1_struct_0(A_15)) | ~m1_subset_1(B_27, u1_struct_0(A_15)) | ~l1_orders_2(A_15) | ~v3_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.94  tff(c_24, plain, (![A_15, C_33, B_27]: (~r1_orders_2(A_15, C_33, B_27) | v6_orders_2('#skF_1'(A_15, B_27, C_33), A_15) | ~m1_subset_1(C_33, u1_struct_0(A_15)) | ~m1_subset_1(B_27, u1_struct_0(A_15)) | ~l1_orders_2(A_15) | ~v3_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.94  tff(c_536, plain, (![A_181, C_182, B_183]: (~r1_orders_2(A_181, C_182, B_183) | m1_subset_1('#skF_1'(A_181, B_183, C_182), k1_zfmisc_1(u1_struct_0(A_181))) | ~m1_subset_1(C_182, u1_struct_0(A_181)) | ~m1_subset_1(B_183, u1_struct_0(A_181)) | ~l1_orders_2(A_181) | ~v3_orders_2(A_181))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.94  tff(c_44, plain, (![D_55]: (v6_orders_2('#skF_5', '#skF_2') | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.94  tff(c_456, plain, (![D_55]: (~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(splitLeft, [status(thm)], [c_44])).
% 4.66/1.94  tff(c_540, plain, (![B_183, C_182]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_183, C_182)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_183, C_182)) | ~v6_orders_2('#skF_1'('#skF_2', B_183, C_182), '#skF_2') | ~r1_orders_2('#skF_2', C_182, B_183) | ~m1_subset_1(C_182, u1_struct_0('#skF_2')) | ~m1_subset_1(B_183, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_536, c_456])).
% 4.66/1.94  tff(c_552, plain, (![B_187, C_188]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_187, C_188)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_187, C_188)) | ~v6_orders_2('#skF_1'('#skF_2', B_187, C_188), '#skF_2') | ~r1_orders_2('#skF_2', C_188, B_187) | ~m1_subset_1(C_188, u1_struct_0('#skF_2')) | ~m1_subset_1(B_187, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_540])).
% 4.66/1.94  tff(c_560, plain, (![B_27, C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, C_33)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_27, C_33)) | ~r1_orders_2('#skF_2', C_33, B_27) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_552])).
% 4.66/1.94  tff(c_586, plain, (![B_193, C_194]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_193, C_194)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_193, C_194)) | ~r1_orders_2('#skF_2', C_194, B_193) | ~m1_subset_1(C_194, u1_struct_0('#skF_2')) | ~m1_subset_1(B_193, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_560])).
% 4.66/1.94  tff(c_598, plain, (![C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_33)) | ~r1_orders_2('#skF_2', C_33, '#skF_3') | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_586])).
% 4.66/1.94  tff(c_630, plain, (![C_196]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_196)) | ~r1_orders_2('#skF_2', C_196, '#skF_3') | ~m1_subset_1(C_196, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_598])).
% 4.66/1.94  tff(c_634, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_12, c_630])).
% 4.66/1.94  tff(c_642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_28, c_88, c_634])).
% 4.66/1.94  tff(c_643, plain, (v6_orders_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.66/1.94  tff(c_18, plain, (![A_15, B_27, C_33]: (~r1_orders_2(A_15, B_27, C_33) | r2_hidden(B_27, '#skF_1'(A_15, B_27, C_33)) | ~m1_subset_1(C_33, u1_struct_0(A_15)) | ~m1_subset_1(B_27, u1_struct_0(A_15)) | ~l1_orders_2(A_15) | ~v3_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.94  tff(c_14, plain, (![A_15, B_27, C_33]: (~r1_orders_2(A_15, B_27, C_33) | r2_hidden(C_33, '#skF_1'(A_15, B_27, C_33)) | ~m1_subset_1(C_33, u1_struct_0(A_15)) | ~m1_subset_1(B_27, u1_struct_0(A_15)) | ~l1_orders_2(A_15) | ~v3_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.94  tff(c_26, plain, (![A_15, B_27, C_33]: (~r1_orders_2(A_15, B_27, C_33) | v6_orders_2('#skF_1'(A_15, B_27, C_33), A_15) | ~m1_subset_1(C_33, u1_struct_0(A_15)) | ~m1_subset_1(B_27, u1_struct_0(A_15)) | ~l1_orders_2(A_15) | ~v3_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.94  tff(c_352, plain, (![A_137, B_138, C_139]: (~r1_orders_2(A_137, B_138, C_139) | m1_subset_1('#skF_1'(A_137, B_138, C_139), k1_zfmisc_1(u1_struct_0(A_137))) | ~m1_subset_1(C_139, u1_struct_0(A_137)) | ~m1_subset_1(B_138, u1_struct_0(A_137)) | ~l1_orders_2(A_137) | ~v3_orders_2(A_137))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.94  tff(c_40, plain, (![D_55]: (r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.94  tff(c_276, plain, (![D_55]: (~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(splitLeft, [status(thm)], [c_40])).
% 4.66/1.94  tff(c_356, plain, (![B_138, C_139]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_138, C_139)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_138, C_139)) | ~v6_orders_2('#skF_1'('#skF_2', B_138, C_139), '#skF_2') | ~r1_orders_2('#skF_2', B_138, C_139) | ~m1_subset_1(C_139, u1_struct_0('#skF_2')) | ~m1_subset_1(B_138, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_352, c_276])).
% 4.66/1.94  tff(c_368, plain, (![B_143, C_144]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_143, C_144)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_143, C_144)) | ~v6_orders_2('#skF_1'('#skF_2', B_143, C_144), '#skF_2') | ~r1_orders_2('#skF_2', B_143, C_144) | ~m1_subset_1(C_144, u1_struct_0('#skF_2')) | ~m1_subset_1(B_143, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_356])).
% 4.66/1.94  tff(c_372, plain, (![B_27, C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, C_33)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_27, C_33)) | ~r1_orders_2('#skF_2', B_27, C_33) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_368])).
% 4.66/1.94  tff(c_398, plain, (![B_147, C_148]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_147, C_148)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_147, C_148)) | ~r1_orders_2('#skF_2', B_147, C_148) | ~m1_subset_1(C_148, u1_struct_0('#skF_2')) | ~m1_subset_1(B_147, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_372])).
% 4.66/1.94  tff(c_414, plain, (![B_27]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, '#skF_3')) | ~r1_orders_2('#skF_2', B_27, '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_398])).
% 4.66/1.94  tff(c_442, plain, (![B_150]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_150, '#skF_3')) | ~r1_orders_2('#skF_2', B_150, '#skF_3') | ~m1_subset_1(B_150, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_414])).
% 4.66/1.94  tff(c_446, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_18, c_442])).
% 4.66/1.94  tff(c_454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_28, c_30, c_88, c_446])).
% 4.66/1.94  tff(c_455, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_40])).
% 4.66/1.94  tff(c_174, plain, (![A_88, B_89, C_90]: (~r1_orders_2(A_88, B_89, C_90) | m1_subset_1('#skF_1'(A_88, B_89, C_90), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(C_90, u1_struct_0(A_88)) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l1_orders_2(A_88) | ~v3_orders_2(A_88))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.94  tff(c_38, plain, (![D_55]: (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.95  tff(c_99, plain, (![D_55]: (~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(splitLeft, [status(thm)], [c_38])).
% 4.66/1.95  tff(c_178, plain, (![B_89, C_90]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_89, C_90)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_89, C_90)) | ~v6_orders_2('#skF_1'('#skF_2', B_89, C_90), '#skF_2') | ~r1_orders_2('#skF_2', B_89, C_90) | ~m1_subset_1(C_90, u1_struct_0('#skF_2')) | ~m1_subset_1(B_89, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_174, c_99])).
% 4.66/1.95  tff(c_190, plain, (![B_94, C_95]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_94, C_95)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_94, C_95)) | ~v6_orders_2('#skF_1'('#skF_2', B_94, C_95), '#skF_2') | ~r1_orders_2('#skF_2', B_94, C_95) | ~m1_subset_1(C_95, u1_struct_0('#skF_2')) | ~m1_subset_1(B_94, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_178])).
% 4.66/1.95  tff(c_198, plain, (![B_27, C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, C_33)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_27, C_33)) | ~r1_orders_2('#skF_2', B_27, C_33) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_190])).
% 4.66/1.95  tff(c_218, plain, (![B_100, C_101]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_100, C_101)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_100, C_101)) | ~r1_orders_2('#skF_2', B_100, C_101) | ~m1_subset_1(C_101, u1_struct_0('#skF_2')) | ~m1_subset_1(B_100, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_198])).
% 4.66/1.95  tff(c_230, plain, (![B_27]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, '#skF_3')) | ~r1_orders_2('#skF_2', B_27, '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_218])).
% 4.66/1.95  tff(c_262, plain, (![B_103]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_103, '#skF_3')) | ~r1_orders_2('#skF_2', B_103, '#skF_3') | ~m1_subset_1(B_103, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_230])).
% 4.66/1.95  tff(c_266, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_18, c_262])).
% 4.66/1.95  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_28, c_30, c_88, c_266])).
% 4.66/1.95  tff(c_275, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 4.66/1.95  tff(c_721, plain, (![A_227, B_228, C_229]: (~r1_orders_2(A_227, B_228, C_229) | m1_subset_1('#skF_1'(A_227, B_228, C_229), k1_zfmisc_1(u1_struct_0(A_227))) | ~m1_subset_1(C_229, u1_struct_0(A_227)) | ~m1_subset_1(B_228, u1_struct_0(A_227)) | ~l1_orders_2(A_227) | ~v3_orders_2(A_227))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.95  tff(c_42, plain, (![D_55]: (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.95  tff(c_644, plain, (![D_55]: (~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(splitLeft, [status(thm)], [c_42])).
% 4.66/1.95  tff(c_725, plain, (![B_228, C_229]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_228, C_229)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_228, C_229)) | ~v6_orders_2('#skF_1'('#skF_2', B_228, C_229), '#skF_2') | ~r1_orders_2('#skF_2', B_228, C_229) | ~m1_subset_1(C_229, u1_struct_0('#skF_2')) | ~m1_subset_1(B_228, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_721, c_644])).
% 4.66/1.95  tff(c_756, plain, (![B_237, C_238]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_237, C_238)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_237, C_238)) | ~v6_orders_2('#skF_1'('#skF_2', B_237, C_238), '#skF_2') | ~r1_orders_2('#skF_2', B_237, C_238) | ~m1_subset_1(C_238, u1_struct_0('#skF_2')) | ~m1_subset_1(B_237, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_725])).
% 4.66/1.95  tff(c_760, plain, (![B_27, C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, C_33)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_27, C_33)) | ~r1_orders_2('#skF_2', B_27, C_33) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_756])).
% 4.66/1.95  tff(c_771, plain, (![B_239, C_240]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_239, C_240)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_239, C_240)) | ~r1_orders_2('#skF_2', B_239, C_240) | ~m1_subset_1(C_240, u1_struct_0('#skF_2')) | ~m1_subset_1(B_239, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_760])).
% 4.66/1.95  tff(c_783, plain, (![B_27]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, '#skF_3')) | ~r1_orders_2('#skF_2', B_27, '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_771])).
% 4.66/1.95  tff(c_800, plain, (![B_241]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_241, '#skF_3')) | ~r1_orders_2('#skF_2', B_241, '#skF_3') | ~m1_subset_1(B_241, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_783])).
% 4.66/1.95  tff(c_808, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_18, c_800])).
% 4.66/1.95  tff(c_815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_28, c_30, c_88, c_808])).
% 4.66/1.95  tff(c_816, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_42])).
% 4.66/1.95  tff(c_52, plain, (![D_55]: (r2_orders_2('#skF_2', '#skF_3', '#skF_4') | ~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.95  tff(c_818, plain, (![D_55]: (r2_orders_2('#skF_2', '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_52])).
% 4.66/1.95  tff(c_819, plain, (![D_55]: (~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_86, c_818])).
% 4.66/1.95  tff(c_823, plain, (~r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_3', '#skF_5') | ~v6_orders_2('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_816, c_819])).
% 4.66/1.95  tff(c_827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_643, c_455, c_275, c_823])).
% 4.66/1.95  tff(c_829, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_87])).
% 4.66/1.95  tff(c_56, plain, (r2_hidden('#skF_3', '#skF_5') | r2_orders_2('#skF_2', '#skF_3', '#skF_4') | r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.95  tff(c_830, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_829, c_86, c_56])).
% 4.66/1.95  tff(c_828, plain, (v6_orders_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_87])).
% 4.66/1.95  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_orders_2('#skF_2', '#skF_3', '#skF_4') | r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.95  tff(c_833, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_829, c_86, c_58])).
% 4.66/1.95  tff(c_54, plain, (r2_hidden('#skF_4', '#skF_5') | r2_orders_2('#skF_2', '#skF_3', '#skF_4') | r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.95  tff(c_832, plain, (r2_hidden('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_829, c_86, c_54])).
% 4.66/1.95  tff(c_885, plain, (![A_278, C_279, B_280, D_281]: (r1_orders_2(A_278, C_279, B_280) | r1_orders_2(A_278, B_280, C_279) | ~r2_hidden(C_279, D_281) | ~r2_hidden(B_280, D_281) | ~m1_subset_1(D_281, k1_zfmisc_1(u1_struct_0(A_278))) | ~v6_orders_2(D_281, A_278) | ~m1_subset_1(C_279, u1_struct_0(A_278)) | ~m1_subset_1(B_280, u1_struct_0(A_278)) | ~l1_orders_2(A_278) | ~v3_orders_2(A_278))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.95  tff(c_904, plain, (![A_282, B_283]: (r1_orders_2(A_282, '#skF_4', B_283) | r1_orders_2(A_282, B_283, '#skF_4') | ~r2_hidden(B_283, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_282))) | ~v6_orders_2('#skF_5', A_282) | ~m1_subset_1('#skF_4', u1_struct_0(A_282)) | ~m1_subset_1(B_283, u1_struct_0(A_282)) | ~l1_orders_2(A_282) | ~v3_orders_2(A_282))), inference(resolution, [status(thm)], [c_832, c_885])).
% 4.66/1.95  tff(c_906, plain, (![B_283]: (r1_orders_2('#skF_2', '#skF_4', B_283) | r1_orders_2('#skF_2', B_283, '#skF_4') | ~r2_hidden(B_283, '#skF_5') | ~v6_orders_2('#skF_5', '#skF_2') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1(B_283, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_833, c_904])).
% 4.66/1.95  tff(c_910, plain, (![B_284]: (r1_orders_2('#skF_2', '#skF_4', B_284) | r1_orders_2('#skF_2', B_284, '#skF_4') | ~r2_hidden(B_284, '#skF_5') | ~m1_subset_1(B_284, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_28, c_828, c_906])).
% 4.66/1.95  tff(c_916, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_3') | r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_910])).
% 4.66/1.95  tff(c_922, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_3') | r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_830, c_916])).
% 4.66/1.95  tff(c_924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_864, c_829, c_922])).
% 4.66/1.95  tff(c_925, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_863])).
% 4.66/1.95  tff(c_926, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_863])).
% 4.66/1.95  tff(c_937, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_925, c_926])).
% 4.66/1.95  tff(c_928, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_925, c_829])).
% 4.66/1.95  tff(c_940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_937, c_928])).
% 4.66/1.95  tff(c_942, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_72])).
% 4.66/1.95  tff(c_1267, plain, (![A_378, B_379, C_380]: (r1_orders_2(A_378, B_379, C_380) | ~r2_orders_2(A_378, B_379, C_380) | ~m1_subset_1(C_380, u1_struct_0(A_378)) | ~m1_subset_1(B_379, u1_struct_0(A_378)) | ~l1_orders_2(A_378))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.66/1.95  tff(c_1269, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_942, c_1267])).
% 4.66/1.95  tff(c_1272, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_1269])).
% 4.66/1.95  tff(c_1322, plain, (![A_407, C_408, B_409]: (~r1_orders_2(A_407, C_408, B_409) | m1_subset_1('#skF_1'(A_407, B_409, C_408), k1_zfmisc_1(u1_struct_0(A_407))) | ~m1_subset_1(C_408, u1_struct_0(A_407)) | ~m1_subset_1(B_409, u1_struct_0(A_407)) | ~l1_orders_2(A_407) | ~v3_orders_2(A_407))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.95  tff(c_1265, plain, (![D_55]: (~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(splitLeft, [status(thm)], [c_44])).
% 4.66/1.95  tff(c_1326, plain, (![B_409, C_408]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_409, C_408)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_409, C_408)) | ~v6_orders_2('#skF_1'('#skF_2', B_409, C_408), '#skF_2') | ~r1_orders_2('#skF_2', C_408, B_409) | ~m1_subset_1(C_408, u1_struct_0('#skF_2')) | ~m1_subset_1(B_409, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_1322, c_1265])).
% 4.66/1.95  tff(c_1338, plain, (![B_413, C_414]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_413, C_414)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_413, C_414)) | ~v6_orders_2('#skF_1'('#skF_2', B_413, C_414), '#skF_2') | ~r1_orders_2('#skF_2', C_414, B_413) | ~m1_subset_1(C_414, u1_struct_0('#skF_2')) | ~m1_subset_1(B_413, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1326])).
% 4.66/1.95  tff(c_1342, plain, (![B_27, C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, C_33)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_27, C_33)) | ~r1_orders_2('#skF_2', C_33, B_27) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1338])).
% 4.66/1.95  tff(c_1368, plain, (![B_417, C_418]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_417, C_418)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_417, C_418)) | ~r1_orders_2('#skF_2', C_418, B_417) | ~m1_subset_1(C_418, u1_struct_0('#skF_2')) | ~m1_subset_1(B_417, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1342])).
% 4.66/1.95  tff(c_1372, plain, (![B_27]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, '#skF_3')) | ~r1_orders_2('#skF_2', '#skF_3', B_27) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_1368])).
% 4.66/1.95  tff(c_1397, plain, (![B_419]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_419, '#skF_3')) | ~r1_orders_2('#skF_2', '#skF_3', B_419) | ~m1_subset_1(B_419, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_1372])).
% 4.66/1.95  tff(c_1401, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_16, c_1397])).
% 4.66/1.95  tff(c_1409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_28, c_30, c_1272, c_1401])).
% 4.66/1.95  tff(c_1410, plain, (v6_orders_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.66/1.95  tff(c_1120, plain, (![A_333, B_334, C_335]: (r1_orders_2(A_333, B_334, C_335) | ~r2_orders_2(A_333, B_334, C_335) | ~m1_subset_1(C_335, u1_struct_0(A_333)) | ~m1_subset_1(B_334, u1_struct_0(A_333)) | ~l1_orders_2(A_333))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.66/1.95  tff(c_1122, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_942, c_1120])).
% 4.66/1.95  tff(c_1125, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_1122])).
% 4.66/1.95  tff(c_1175, plain, (![A_362, C_363, B_364]: (~r1_orders_2(A_362, C_363, B_364) | m1_subset_1('#skF_1'(A_362, B_364, C_363), k1_zfmisc_1(u1_struct_0(A_362))) | ~m1_subset_1(C_363, u1_struct_0(A_362)) | ~m1_subset_1(B_364, u1_struct_0(A_362)) | ~l1_orders_2(A_362) | ~v3_orders_2(A_362))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.95  tff(c_1118, plain, (![D_55]: (~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(splitLeft, [status(thm)], [c_40])).
% 4.66/1.95  tff(c_1179, plain, (![B_364, C_363]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_364, C_363)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_364, C_363)) | ~v6_orders_2('#skF_1'('#skF_2', B_364, C_363), '#skF_2') | ~r1_orders_2('#skF_2', C_363, B_364) | ~m1_subset_1(C_363, u1_struct_0('#skF_2')) | ~m1_subset_1(B_364, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_1175, c_1118])).
% 4.66/1.95  tff(c_1191, plain, (![B_368, C_369]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_368, C_369)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_368, C_369)) | ~v6_orders_2('#skF_1'('#skF_2', B_368, C_369), '#skF_2') | ~r1_orders_2('#skF_2', C_369, B_368) | ~m1_subset_1(C_369, u1_struct_0('#skF_2')) | ~m1_subset_1(B_368, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1179])).
% 4.66/1.95  tff(c_1199, plain, (![B_27, C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, C_33)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_27, C_33)) | ~r1_orders_2('#skF_2', C_33, B_27) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1191])).
% 4.66/1.95  tff(c_1222, plain, (![B_374, C_375]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_374, C_375)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_374, C_375)) | ~r1_orders_2('#skF_2', C_375, B_374) | ~m1_subset_1(C_375, u1_struct_0('#skF_2')) | ~m1_subset_1(B_374, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1199])).
% 4.66/1.95  tff(c_1226, plain, (![B_27]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, '#skF_3')) | ~r1_orders_2('#skF_2', '#skF_3', B_27) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_1222])).
% 4.66/1.95  tff(c_1251, plain, (![B_376]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_376, '#skF_3')) | ~r1_orders_2('#skF_2', '#skF_3', B_376) | ~m1_subset_1(B_376, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_1226])).
% 4.66/1.95  tff(c_1255, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_16, c_1251])).
% 4.66/1.95  tff(c_1263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_28, c_30, c_1125, c_1255])).
% 4.66/1.95  tff(c_1264, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_40])).
% 4.66/1.95  tff(c_959, plain, (![A_289, B_290, C_291]: (r1_orders_2(A_289, B_290, C_291) | ~r2_orders_2(A_289, B_290, C_291) | ~m1_subset_1(C_291, u1_struct_0(A_289)) | ~m1_subset_1(B_290, u1_struct_0(A_289)) | ~l1_orders_2(A_289))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.66/1.95  tff(c_961, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_942, c_959])).
% 4.66/1.95  tff(c_964, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_961])).
% 4.66/1.95  tff(c_1014, plain, (![A_318, C_319, B_320]: (~r1_orders_2(A_318, C_319, B_320) | m1_subset_1('#skF_1'(A_318, B_320, C_319), k1_zfmisc_1(u1_struct_0(A_318))) | ~m1_subset_1(C_319, u1_struct_0(A_318)) | ~m1_subset_1(B_320, u1_struct_0(A_318)) | ~l1_orders_2(A_318) | ~v3_orders_2(A_318))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.95  tff(c_957, plain, (![D_55]: (~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(splitLeft, [status(thm)], [c_38])).
% 4.66/1.95  tff(c_1018, plain, (![B_320, C_319]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_320, C_319)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_320, C_319)) | ~v6_orders_2('#skF_1'('#skF_2', B_320, C_319), '#skF_2') | ~r1_orders_2('#skF_2', C_319, B_320) | ~m1_subset_1(C_319, u1_struct_0('#skF_2')) | ~m1_subset_1(B_320, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_1014, c_957])).
% 4.66/1.95  tff(c_1030, plain, (![B_324, C_325]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_324, C_325)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_324, C_325)) | ~v6_orders_2('#skF_1'('#skF_2', B_324, C_325), '#skF_2') | ~r1_orders_2('#skF_2', C_325, B_324) | ~m1_subset_1(C_325, u1_struct_0('#skF_2')) | ~m1_subset_1(B_324, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1018])).
% 4.66/1.95  tff(c_1034, plain, (![B_27, C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, C_33)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_27, C_33)) | ~r1_orders_2('#skF_2', C_33, B_27) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1030])).
% 4.66/1.95  tff(c_1060, plain, (![B_328, C_329]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_328, C_329)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_328, C_329)) | ~r1_orders_2('#skF_2', C_329, B_328) | ~m1_subset_1(C_329, u1_struct_0('#skF_2')) | ~m1_subset_1(B_328, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1034])).
% 4.66/1.95  tff(c_1068, plain, (![B_27]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, '#skF_3')) | ~r1_orders_2('#skF_2', '#skF_3', B_27) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_1060])).
% 4.66/1.95  tff(c_1104, plain, (![B_331]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_331, '#skF_3')) | ~r1_orders_2('#skF_2', '#skF_3', B_331) | ~m1_subset_1(B_331, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_1068])).
% 4.66/1.95  tff(c_1108, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_16, c_1104])).
% 4.66/1.95  tff(c_1116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_28, c_30, c_964, c_1108])).
% 4.66/1.95  tff(c_1117, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 4.66/1.95  tff(c_1411, plain, (![A_420, B_421, C_422]: (r1_orders_2(A_420, B_421, C_422) | ~r2_orders_2(A_420, B_421, C_422) | ~m1_subset_1(C_422, u1_struct_0(A_420)) | ~m1_subset_1(B_421, u1_struct_0(A_420)) | ~l1_orders_2(A_420))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.66/1.95  tff(c_1413, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_942, c_1411])).
% 4.66/1.95  tff(c_1416, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_1413])).
% 4.66/1.95  tff(c_1468, plain, (![A_450, C_451, B_452]: (~r1_orders_2(A_450, C_451, B_452) | m1_subset_1('#skF_1'(A_450, B_452, C_451), k1_zfmisc_1(u1_struct_0(A_450))) | ~m1_subset_1(C_451, u1_struct_0(A_450)) | ~m1_subset_1(B_452, u1_struct_0(A_450)) | ~l1_orders_2(A_450) | ~v3_orders_2(A_450))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.66/1.95  tff(c_1417, plain, (![D_55]: (~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(splitLeft, [status(thm)], [c_42])).
% 4.66/1.95  tff(c_1472, plain, (![B_452, C_451]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_452, C_451)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_452, C_451)) | ~v6_orders_2('#skF_1'('#skF_2', B_452, C_451), '#skF_2') | ~r1_orders_2('#skF_2', C_451, B_452) | ~m1_subset_1(C_451, u1_struct_0('#skF_2')) | ~m1_subset_1(B_452, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_1468, c_1417])).
% 4.66/1.95  tff(c_1484, plain, (![B_456, C_457]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_456, C_457)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_456, C_457)) | ~v6_orders_2('#skF_1'('#skF_2', B_456, C_457), '#skF_2') | ~r1_orders_2('#skF_2', C_457, B_456) | ~m1_subset_1(C_457, u1_struct_0('#skF_2')) | ~m1_subset_1(B_456, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1472])).
% 4.66/1.95  tff(c_1488, plain, (![B_27, C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, C_33)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_27, C_33)) | ~r1_orders_2('#skF_2', C_33, B_27) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1484])).
% 4.66/1.95  tff(c_1499, plain, (![B_458, C_459]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_458, C_459)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_458, C_459)) | ~r1_orders_2('#skF_2', C_459, B_458) | ~m1_subset_1(C_459, u1_struct_0('#skF_2')) | ~m1_subset_1(B_458, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1488])).
% 4.66/1.95  tff(c_1503, plain, (![B_27]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, '#skF_3')) | ~r1_orders_2('#skF_2', '#skF_3', B_27) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_1499])).
% 4.66/1.95  tff(c_1528, plain, (![B_460]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_460, '#skF_3')) | ~r1_orders_2('#skF_2', '#skF_3', B_460) | ~m1_subset_1(B_460, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_1503])).
% 4.66/1.95  tff(c_1532, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_16, c_1528])).
% 4.66/1.95  tff(c_1540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_28, c_30, c_1416, c_1532])).
% 4.66/1.95  tff(c_1541, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_42])).
% 4.66/1.95  tff(c_941, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 4.66/1.95  tff(c_943, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_941])).
% 4.66/1.95  tff(c_46, plain, (![D_55]: (r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~r2_orders_2('#skF_2', '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.66/1.95  tff(c_1582, plain, (![D_55]: (r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_942, c_46])).
% 4.66/1.95  tff(c_1584, plain, (![D_469]: (~r2_hidden('#skF_4', D_469) | ~r2_hidden('#skF_3', D_469) | ~m1_subset_1(D_469, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_469, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_943, c_1582])).
% 4.66/1.95  tff(c_1587, plain, (~r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_3', '#skF_5') | ~v6_orders_2('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_1541, c_1584])).
% 4.66/1.95  tff(c_1591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1410, c_1264, c_1117, c_1587])).
% 4.66/1.95  tff(c_1593, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_941])).
% 4.66/1.95  tff(c_1678, plain, (![A_478, C_479, B_480]: (~r2_orders_2(A_478, C_479, B_480) | ~r1_orders_2(A_478, B_480, C_479) | ~m1_subset_1(C_479, u1_struct_0(A_478)) | ~m1_subset_1(B_480, u1_struct_0(A_478)) | ~l1_orders_2(A_478) | ~v5_orders_2(A_478))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.66/1.95  tff(c_1680, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_942, c_1678])).
% 4.66/1.95  tff(c_1684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_30, c_1593, c_1680])).
% 4.66/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.95  
% 4.66/1.95  Inference rules
% 4.66/1.95  ----------------------
% 4.66/1.95  #Ref     : 0
% 4.66/1.95  #Sup     : 225
% 4.66/1.95  #Fact    : 0
% 4.66/1.95  #Define  : 0
% 4.66/1.95  #Split   : 22
% 4.66/1.95  #Chain   : 0
% 4.66/1.95  #Close   : 0
% 4.66/1.95  
% 4.66/1.95  Ordering : KBO
% 4.66/1.95  
% 4.66/1.95  Simplification rules
% 4.66/1.95  ----------------------
% 4.66/1.95  #Subsume      : 76
% 4.66/1.95  #Demod        : 503
% 4.66/1.95  #Tautology    : 86
% 4.66/1.95  #SimpNegUnit  : 31
% 4.66/1.95  #BackRed      : 36
% 4.66/1.95  
% 4.66/1.95  #Partial instantiations: 0
% 4.66/1.95  #Strategies tried      : 1
% 4.66/1.95  
% 4.66/1.95  Timing (in seconds)
% 4.66/1.95  ----------------------
% 4.66/1.95  Preprocessing        : 0.37
% 4.66/1.95  Parsing              : 0.19
% 4.66/1.95  CNF conversion       : 0.03
% 4.66/1.95  Main loop            : 0.69
% 4.66/1.95  Inferencing          : 0.27
% 4.66/1.95  Reduction            : 0.19
% 4.66/1.95  Demodulation         : 0.13
% 4.66/1.95  BG Simplification    : 0.03
% 4.66/1.95  Subsumption          : 0.15
% 4.66/1.95  Abstraction          : 0.03
% 4.66/1.95  MUC search           : 0.00
% 4.66/1.95  Cooper               : 0.00
% 4.66/1.95  Total                : 1.15
% 4.66/1.95  Index Insertion      : 0.00
% 4.66/1.95  Index Deletion       : 0.00
% 4.66/1.95  Index Matching       : 0.00
% 4.66/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
