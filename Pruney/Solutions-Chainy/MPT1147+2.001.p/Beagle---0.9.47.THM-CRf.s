%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:22 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 519 expanded)
%              Number of leaves         :   22 ( 189 expanded)
%              Depth                    :   12
%              Number of atoms          :  546 (2847 expanded)
%              Number of equality atoms :   18 (  47 expanded)
%              Maximal formula depth    :   15 (   5 average)
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

tff(f_124,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(f_97,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_orders_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_orders_2(A,B,C)
                  & r1_orders_2(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_36,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_72,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_86,plain,(
    ~ r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_853,plain,(
    ! [A_247,B_248,C_249] :
      ( r2_orders_2(A_247,B_248,C_249)
      | C_249 = B_248
      | ~ r1_orders_2(A_247,B_248,C_249)
      | ~ m1_subset_1(C_249,u1_struct_0(A_247))
      | ~ m1_subset_1(B_248,u1_struct_0(A_247))
      | ~ l1_orders_2(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_855,plain,(
    ! [B_248] :
      ( r2_orders_2('#skF_2',B_248,'#skF_4')
      | B_248 = '#skF_4'
      | ~ r1_orders_2('#skF_2',B_248,'#skF_4')
      | ~ m1_subset_1(B_248,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_853])).

tff(c_865,plain,(
    ! [B_250] :
      ( r2_orders_2('#skF_2',B_250,'#skF_4')
      | B_250 = '#skF_4'
      | ~ r1_orders_2('#skF_2',B_250,'#skF_4')
      | ~ m1_subset_1(B_250,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_855])).

tff(c_871,plain,
    ( r2_orders_2('#skF_2','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_865])).

tff(c_876,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_871])).

tff(c_877,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_876])).

tff(c_60,plain,
    ( v6_orders_2('#skF_5','#skF_2')
    | r2_orders_2('#skF_2','#skF_3','#skF_4')
    | r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_87,plain,
    ( v6_orders_2('#skF_5','#skF_2')
    | r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_60])).

tff(c_88,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_18,plain,(
    ! [A_15,B_27,C_33] :
      ( ~ r1_orders_2(A_15,B_27,C_33)
      | r2_hidden(B_27,'#skF_1'(A_15,B_27,C_33))
      | ~ m1_subset_1(C_33,u1_struct_0(A_15))
      | ~ m1_subset_1(B_27,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15)
      | ~ v3_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_14,plain,(
    ! [A_15,B_27,C_33] :
      ( ~ r1_orders_2(A_15,B_27,C_33)
      | r2_hidden(C_33,'#skF_1'(A_15,B_27,C_33))
      | ~ m1_subset_1(C_33,u1_struct_0(A_15))
      | ~ m1_subset_1(B_27,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15)
      | ~ v3_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    ! [A_15,B_27,C_33] :
      ( ~ r1_orders_2(A_15,B_27,C_33)
      | v6_orders_2('#skF_1'(A_15,B_27,C_33),A_15)
      | ~ m1_subset_1(C_33,u1_struct_0(A_15))
      | ~ m1_subset_1(B_27,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15)
      | ~ v3_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_529,plain,(
    ! [A_180,B_181,C_182] :
      ( ~ r1_orders_2(A_180,B_181,C_182)
      | m1_subset_1('#skF_1'(A_180,B_181,C_182),k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ m1_subset_1(C_182,u1_struct_0(A_180))
      | ~ m1_subset_1(B_181,u1_struct_0(A_180))
      | ~ l1_orders_2(A_180)
      | ~ v3_orders_2(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    ! [D_55] :
      ( v6_orders_2('#skF_5','#skF_2')
      | ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_450,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_533,plain,(
    ! [B_181,C_182] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_181,C_182))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_181,C_182))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_181,C_182),'#skF_2')
      | ~ r1_orders_2('#skF_2',B_181,C_182)
      | ~ m1_subset_1(C_182,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_181,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_529,c_450])).

tff(c_545,plain,(
    ! [B_186,C_187] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_186,C_187))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_186,C_187))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_186,C_187),'#skF_2')
      | ~ r1_orders_2('#skF_2',B_186,C_187)
      | ~ m1_subset_1(C_187,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_186,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_533])).

tff(c_549,plain,(
    ! [B_27,C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,C_33))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_27,C_33))
      | ~ r1_orders_2('#skF_2',B_27,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_545])).

tff(c_560,plain,(
    ! [B_188,C_189] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_188,C_189))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_188,C_189))
      | ~ r1_orders_2('#skF_2',B_188,C_189)
      | ~ m1_subset_1(C_189,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_188,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_549])).

tff(c_564,plain,(
    ! [B_27] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,'#skF_3'))
      | ~ r1_orders_2('#skF_2',B_27,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_560])).

tff(c_608,plain,(
    ! [B_194] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_194,'#skF_3'))
      | ~ r1_orders_2('#skF_2',B_194,'#skF_3')
      | ~ m1_subset_1(B_194,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_564])).

tff(c_612,plain,
    ( ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_608])).

tff(c_620,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_28,c_30,c_88,c_612])).

tff(c_621,plain,(
    v6_orders_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_12,plain,(
    ! [A_15,C_33,B_27] :
      ( ~ r1_orders_2(A_15,C_33,B_27)
      | r2_hidden(C_33,'#skF_1'(A_15,B_27,C_33))
      | ~ m1_subset_1(C_33,u1_struct_0(A_15))
      | ~ m1_subset_1(B_27,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15)
      | ~ v3_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16,plain,(
    ! [A_15,C_33,B_27] :
      ( ~ r1_orders_2(A_15,C_33,B_27)
      | r2_hidden(B_27,'#skF_1'(A_15,B_27,C_33))
      | ~ m1_subset_1(C_33,u1_struct_0(A_15))
      | ~ m1_subset_1(B_27,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15)
      | ~ v3_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    ! [A_15,C_33,B_27] :
      ( ~ r1_orders_2(A_15,C_33,B_27)
      | v6_orders_2('#skF_1'(A_15,B_27,C_33),A_15)
      | ~ m1_subset_1(C_33,u1_struct_0(A_15))
      | ~ m1_subset_1(B_27,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15)
      | ~ v3_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_373,plain,(
    ! [A_139,C_140,B_141] :
      ( ~ r1_orders_2(A_139,C_140,B_141)
      | m1_subset_1('#skF_1'(A_139,B_141,C_140),k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ m1_subset_1(C_140,u1_struct_0(A_139))
      | ~ m1_subset_1(B_141,u1_struct_0(A_139))
      | ~ l1_orders_2(A_139)
      | ~ v3_orders_2(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    ! [D_55] :
      ( r2_hidden('#skF_3','#skF_5')
      | ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_296,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_377,plain,(
    ! [B_141,C_140] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_141,C_140))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_141,C_140))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_141,C_140),'#skF_2')
      | ~ r1_orders_2('#skF_2',C_140,B_141)
      | ~ m1_subset_1(C_140,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_373,c_296])).

tff(c_389,plain,(
    ! [B_145,C_146] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_145,C_146))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_145,C_146))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_145,C_146),'#skF_2')
      | ~ r1_orders_2('#skF_2',C_146,B_145)
      | ~ m1_subset_1(C_146,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_377])).

tff(c_393,plain,(
    ! [B_27,C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,C_33))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_27,C_33))
      | ~ r1_orders_2('#skF_2',C_33,B_27)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_389])).

tff(c_404,plain,(
    ! [B_147,C_148] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_147,C_148))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_147,C_148))
      | ~ r1_orders_2('#skF_2',C_148,B_147)
      | ~ m1_subset_1(C_148,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_147,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_393])).

tff(c_416,plain,(
    ! [C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_33))
      | ~ r1_orders_2('#skF_2',C_33,'#skF_3')
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_404])).

tff(c_433,plain,(
    ! [C_149] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_149))
      | ~ r1_orders_2('#skF_2',C_149,'#skF_3')
      | ~ m1_subset_1(C_149,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_416])).

tff(c_441,plain,
    ( ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_433])).

tff(c_448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_28,c_88,c_441])).

tff(c_449,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_176,plain,(
    ! [A_88,C_89,B_90] :
      ( ~ r1_orders_2(A_88,C_89,B_90)
      | m1_subset_1('#skF_1'(A_88,B_90,C_89),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(C_89,u1_struct_0(A_88))
      | ~ m1_subset_1(B_90,u1_struct_0(A_88))
      | ~ l1_orders_2(A_88)
      | ~ v3_orders_2(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    ! [D_55] :
      ( r2_hidden('#skF_4','#skF_5')
      | ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_99,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_180,plain,(
    ! [B_90,C_89] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_90,C_89))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_90,C_89))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_90,C_89),'#skF_2')
      | ~ r1_orders_2('#skF_2',C_89,B_90)
      | ~ m1_subset_1(C_89,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_90,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_176,c_99])).

tff(c_205,plain,(
    ! [B_98,C_99] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_98,C_99))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_98,C_99))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_98,C_99),'#skF_2')
      | ~ r1_orders_2('#skF_2',C_99,B_98)
      | ~ m1_subset_1(C_99,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_98,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_180])).

tff(c_213,plain,(
    ! [B_27,C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,C_33))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_27,C_33))
      | ~ r1_orders_2('#skF_2',C_33,B_27)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_205])).

tff(c_220,plain,(
    ! [B_100,C_101] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_100,C_101))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_100,C_101))
      | ~ r1_orders_2('#skF_2',C_101,B_100)
      | ~ m1_subset_1(C_101,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_213])).

tff(c_236,plain,(
    ! [C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_33))
      | ~ r1_orders_2('#skF_2',C_33,'#skF_3')
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_220])).

tff(c_279,plain,(
    ! [C_105] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_105))
      | ~ r1_orders_2('#skF_2',C_105,'#skF_3')
      | ~ m1_subset_1(C_105,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_236])).

tff(c_287,plain,
    ( ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_279])).

tff(c_294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_28,c_88,c_287])).

tff(c_295,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_702,plain,(
    ! [A_225,B_226,C_227] :
      ( ~ r1_orders_2(A_225,B_226,C_227)
      | m1_subset_1('#skF_1'(A_225,B_226,C_227),k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ m1_subset_1(C_227,u1_struct_0(A_225))
      | ~ m1_subset_1(B_226,u1_struct_0(A_225))
      | ~ l1_orders_2(A_225)
      | ~ v3_orders_2(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    ! [D_55] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_623,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_706,plain,(
    ! [B_226,C_227] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_226,C_227))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_226,C_227))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_226,C_227),'#skF_2')
      | ~ r1_orders_2('#skF_2',B_226,C_227)
      | ~ m1_subset_1(C_227,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_226,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_702,c_623])).

tff(c_718,plain,(
    ! [B_231,C_232] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_231,C_232))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_231,C_232))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_231,C_232),'#skF_2')
      | ~ r1_orders_2('#skF_2',B_231,C_232)
      | ~ m1_subset_1(C_232,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_231,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_706])).

tff(c_726,plain,(
    ! [B_27,C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,C_33))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_27,C_33))
      | ~ r1_orders_2('#skF_2',B_27,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_718])).

tff(c_733,plain,(
    ! [B_233,C_234] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_233,C_234))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_233,C_234))
      | ~ r1_orders_2('#skF_2',B_233,C_234)
      | ~ m1_subset_1(C_234,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_233,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_726])).

tff(c_745,plain,(
    ! [B_27] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,'#skF_3'))
      | ~ r1_orders_2('#skF_2',B_27,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_733])).

tff(c_792,plain,(
    ! [B_238] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_238,'#skF_3'))
      | ~ r1_orders_2('#skF_2',B_238,'#skF_3')
      | ~ m1_subset_1(B_238,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_745])).

tff(c_796,plain,
    ( ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_792])).

tff(c_804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_28,c_30,c_88,c_796])).

tff(c_805,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_831,plain,(
    ! [D_55] :
      ( r2_orders_2('#skF_2','#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_52])).

tff(c_833,plain,(
    ! [D_243] :
      ( ~ r2_hidden('#skF_4',D_243)
      | ~ r2_hidden('#skF_3',D_243)
      | ~ m1_subset_1(D_243,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_243,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_831])).

tff(c_836,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_3','#skF_5')
    | ~ v6_orders_2('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_805,c_833])).

tff(c_840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_449,c_295,c_836])).

tff(c_842,plain,(
    ~ r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_56,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_orders_2('#skF_2','#skF_3','#skF_4')
    | r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_843,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_842,c_86,c_56])).

tff(c_841,plain,(
    v6_orders_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_58,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | r2_orders_2('#skF_2','#skF_3','#skF_4')
    | r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_846,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_842,c_86,c_58])).

tff(c_54,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_orders_2('#skF_2','#skF_3','#skF_4')
    | r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_845,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_842,c_86,c_54])).

tff(c_898,plain,(
    ! [A_279,C_280,B_281,D_282] :
      ( r1_orders_2(A_279,C_280,B_281)
      | r1_orders_2(A_279,B_281,C_280)
      | ~ r2_hidden(C_280,D_282)
      | ~ r2_hidden(B_281,D_282)
      | ~ m1_subset_1(D_282,k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ v6_orders_2(D_282,A_279)
      | ~ m1_subset_1(C_280,u1_struct_0(A_279))
      | ~ m1_subset_1(B_281,u1_struct_0(A_279))
      | ~ l1_orders_2(A_279)
      | ~ v3_orders_2(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_917,plain,(
    ! [A_283,B_284] :
      ( r1_orders_2(A_283,'#skF_4',B_284)
      | r1_orders_2(A_283,B_284,'#skF_4')
      | ~ r2_hidden(B_284,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_283)))
      | ~ v6_orders_2('#skF_5',A_283)
      | ~ m1_subset_1('#skF_4',u1_struct_0(A_283))
      | ~ m1_subset_1(B_284,u1_struct_0(A_283))
      | ~ l1_orders_2(A_283)
      | ~ v3_orders_2(A_283) ) ),
    inference(resolution,[status(thm)],[c_845,c_898])).

tff(c_919,plain,(
    ! [B_284] :
      ( r1_orders_2('#skF_2','#skF_4',B_284)
      | r1_orders_2('#skF_2',B_284,'#skF_4')
      | ~ r2_hidden(B_284,'#skF_5')
      | ~ v6_orders_2('#skF_5','#skF_2')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_284,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_846,c_917])).

tff(c_923,plain,(
    ! [B_285] :
      ( r1_orders_2('#skF_2','#skF_4',B_285)
      | r1_orders_2('#skF_2',B_285,'#skF_4')
      | ~ r2_hidden(B_285,'#skF_5')
      | ~ m1_subset_1(B_285,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_28,c_841,c_919])).

tff(c_929,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_3')
    | r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_923])).

tff(c_935,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_3')
    | r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_929])).

tff(c_937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_877,c_842,c_935])).

tff(c_938,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_939,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_950,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_939])).

tff(c_941,plain,(
    ~ r1_orders_2('#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_842])).

tff(c_955,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_950,c_941])).

tff(c_957,plain,(
    r2_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1400,plain,(
    ! [A_414,B_415,C_416] :
      ( r1_orders_2(A_414,B_415,C_416)
      | ~ r2_orders_2(A_414,B_415,C_416)
      | ~ m1_subset_1(C_416,u1_struct_0(A_414))
      | ~ m1_subset_1(B_415,u1_struct_0(A_414))
      | ~ l1_orders_2(A_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1402,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_957,c_1400])).

tff(c_1405,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_1402])).

tff(c_1457,plain,(
    ! [A_444,B_445,C_446] :
      ( ~ r1_orders_2(A_444,B_445,C_446)
      | m1_subset_1('#skF_1'(A_444,B_445,C_446),k1_zfmisc_1(u1_struct_0(A_444)))
      | ~ m1_subset_1(C_446,u1_struct_0(A_444))
      | ~ m1_subset_1(B_445,u1_struct_0(A_444))
      | ~ l1_orders_2(A_444)
      | ~ v3_orders_2(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_956,plain,
    ( ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_958,plain,(
    ~ r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_956])).

tff(c_46,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_2','#skF_4','#skF_3')
      | ~ r2_orders_2('#skF_2','#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1408,plain,(
    ! [D_55] :
      ( r1_orders_2('#skF_2','#skF_4','#skF_3')
      | ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_957,c_46])).

tff(c_1409,plain,(
    ! [D_55] :
      ( ~ r2_hidden('#skF_4',D_55)
      | ~ r2_hidden('#skF_3',D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v6_orders_2(D_55,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_958,c_1408])).

tff(c_1461,plain,(
    ! [B_445,C_446] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_445,C_446))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_445,C_446))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_445,C_446),'#skF_2')
      | ~ r1_orders_2('#skF_2',B_445,C_446)
      | ~ m1_subset_1(C_446,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_445,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1457,c_1409])).

tff(c_1473,plain,(
    ! [B_450,C_451] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_450,C_451))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_450,C_451))
      | ~ v6_orders_2('#skF_1'('#skF_2',B_450,C_451),'#skF_2')
      | ~ r1_orders_2('#skF_2',B_450,C_451)
      | ~ m1_subset_1(C_451,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_450,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1461])).

tff(c_1477,plain,(
    ! [B_27,C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_27,C_33))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_27,C_33))
      | ~ r1_orders_2('#skF_2',B_27,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_1473])).

tff(c_1507,plain,(
    ! [B_456,C_457] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_456,C_457))
      | ~ r2_hidden('#skF_3','#skF_1'('#skF_2',B_456,C_457))
      | ~ r1_orders_2('#skF_2',B_456,C_457)
      | ~ m1_subset_1(C_457,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_456,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1477])).

tff(c_1515,plain,(
    ! [C_33] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_33))
      | ~ r1_orders_2('#skF_2','#skF_3',C_33)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_1507])).

tff(c_1551,plain,(
    ! [C_459] :
      ( ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_459))
      | ~ r1_orders_2('#skF_2','#skF_3',C_459)
      | ~ m1_subset_1(C_459,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_1515])).

tff(c_1555,plain,
    ( ~ r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_1551])).

tff(c_1563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_28,c_1405,c_1555])).

tff(c_1565,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_956])).

tff(c_1586,plain,(
    ! [A_463,B_464,C_465] :
      ( r2_orders_2(A_463,B_464,C_465)
      | C_465 = B_464
      | ~ r1_orders_2(A_463,B_464,C_465)
      | ~ m1_subset_1(C_465,u1_struct_0(A_463))
      | ~ m1_subset_1(B_464,u1_struct_0(A_463))
      | ~ l1_orders_2(A_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1590,plain,(
    ! [B_464] :
      ( r2_orders_2('#skF_2',B_464,'#skF_3')
      | B_464 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_464,'#skF_3')
      | ~ m1_subset_1(B_464,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_1586])).

tff(c_1610,plain,(
    ! [B_470] :
      ( r2_orders_2('#skF_2',B_470,'#skF_3')
      | B_470 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_470,'#skF_3')
      | ~ m1_subset_1(B_470,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1590])).

tff(c_1613,plain,
    ( r2_orders_2('#skF_2','#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1610])).

tff(c_1619,plain,
    ( r2_orders_2('#skF_2','#skF_4','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1565,c_1613])).

tff(c_1622,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1619])).

tff(c_1629,plain,(
    r2_orders_2('#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1622,c_957])).

tff(c_4,plain,(
    ! [A_1,C_7] :
      ( ~ r2_orders_2(A_1,C_7,C_7)
      | ~ m1_subset_1(C_7,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1641,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1629,c_4])).

tff(c_1648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_1641])).

tff(c_1650,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1619])).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1579,plain,(
    ! [A_460,B_461,C_462] :
      ( r1_orders_2(A_460,B_461,C_462)
      | ~ r2_orders_2(A_460,B_461,C_462)
      | ~ m1_subset_1(C_462,u1_struct_0(A_460))
      | ~ m1_subset_1(B_461,u1_struct_0(A_460))
      | ~ l1_orders_2(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1581,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_957,c_1579])).

tff(c_1584,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_1581])).

tff(c_1658,plain,(
    ! [C_477,B_478,A_479] :
      ( C_477 = B_478
      | ~ r1_orders_2(A_479,C_477,B_478)
      | ~ r1_orders_2(A_479,B_478,C_477)
      | ~ m1_subset_1(C_477,u1_struct_0(A_479))
      | ~ m1_subset_1(B_478,u1_struct_0(A_479))
      | ~ l1_orders_2(A_479)
      | ~ v5_orders_2(A_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1660,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1584,c_1658])).

tff(c_1665,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_30,c_1565,c_1660])).

tff(c_1667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1650,c_1665])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:05:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.85  
% 4.37/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.86  %$ r2_orders_2 > r1_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v3_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.37/1.86  
% 4.37/1.86  %Foreground sorts:
% 4.37/1.86  
% 4.37/1.86  
% 4.37/1.86  %Background operators:
% 4.37/1.86  
% 4.37/1.86  
% 4.37/1.86  %Foreground operators:
% 4.37/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.37/1.86  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.37/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.37/1.86  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.37/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.37/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.37/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.37/1.86  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.37/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.37/1.86  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.37/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.37/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.86  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 4.37/1.86  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 4.37/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.37/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.37/1.86  
% 4.37/1.89  tff(f_124, negated_conjecture, ~(![A]: (((v3_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((?[D]: (((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) & r2_hidden(B, D)) & r2_hidden(C, D))) <=> (r2_orders_2(A, B, C) <=> ~r1_orders_2(A, C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_orders_2)).
% 4.37/1.89  tff(f_40, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 4.37/1.89  tff(f_97, axiom, (![A]: ((v3_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~(((?[D]: (((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) & r2_hidden(B, D)) & r2_hidden(C, D))) & ~r1_orders_2(A, B, C)) & ~r1_orders_2(A, C, B)) & ~((r1_orders_2(A, B, C) | r1_orders_2(A, C, B)) & (![D]: ((v6_orders_2(D, A) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~(r2_hidden(B, D) & r2_hidden(C, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_orders_2)).
% 4.37/1.89  tff(f_56, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_orders_2)).
% 4.37/1.89  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_36, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_72, plain, (r2_hidden('#skF_3', '#skF_5') | ~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_86, plain, (~r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_72])).
% 4.37/1.89  tff(c_853, plain, (![A_247, B_248, C_249]: (r2_orders_2(A_247, B_248, C_249) | C_249=B_248 | ~r1_orders_2(A_247, B_248, C_249) | ~m1_subset_1(C_249, u1_struct_0(A_247)) | ~m1_subset_1(B_248, u1_struct_0(A_247)) | ~l1_orders_2(A_247))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.37/1.89  tff(c_855, plain, (![B_248]: (r2_orders_2('#skF_2', B_248, '#skF_4') | B_248='#skF_4' | ~r1_orders_2('#skF_2', B_248, '#skF_4') | ~m1_subset_1(B_248, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_853])).
% 4.37/1.89  tff(c_865, plain, (![B_250]: (r2_orders_2('#skF_2', B_250, '#skF_4') | B_250='#skF_4' | ~r1_orders_2('#skF_2', B_250, '#skF_4') | ~m1_subset_1(B_250, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_855])).
% 4.37/1.89  tff(c_871, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4') | '#skF_3'='#skF_4' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_865])).
% 4.37/1.89  tff(c_876, plain, ('#skF_3'='#skF_4' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_86, c_871])).
% 4.37/1.89  tff(c_877, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_876])).
% 4.37/1.89  tff(c_60, plain, (v6_orders_2('#skF_5', '#skF_2') | r2_orders_2('#skF_2', '#skF_3', '#skF_4') | r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_87, plain, (v6_orders_2('#skF_5', '#skF_2') | r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_86, c_60])).
% 4.37/1.89  tff(c_88, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_87])).
% 4.37/1.89  tff(c_18, plain, (![A_15, B_27, C_33]: (~r1_orders_2(A_15, B_27, C_33) | r2_hidden(B_27, '#skF_1'(A_15, B_27, C_33)) | ~m1_subset_1(C_33, u1_struct_0(A_15)) | ~m1_subset_1(B_27, u1_struct_0(A_15)) | ~l1_orders_2(A_15) | ~v3_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.37/1.89  tff(c_14, plain, (![A_15, B_27, C_33]: (~r1_orders_2(A_15, B_27, C_33) | r2_hidden(C_33, '#skF_1'(A_15, B_27, C_33)) | ~m1_subset_1(C_33, u1_struct_0(A_15)) | ~m1_subset_1(B_27, u1_struct_0(A_15)) | ~l1_orders_2(A_15) | ~v3_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.37/1.89  tff(c_26, plain, (![A_15, B_27, C_33]: (~r1_orders_2(A_15, B_27, C_33) | v6_orders_2('#skF_1'(A_15, B_27, C_33), A_15) | ~m1_subset_1(C_33, u1_struct_0(A_15)) | ~m1_subset_1(B_27, u1_struct_0(A_15)) | ~l1_orders_2(A_15) | ~v3_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.37/1.89  tff(c_529, plain, (![A_180, B_181, C_182]: (~r1_orders_2(A_180, B_181, C_182) | m1_subset_1('#skF_1'(A_180, B_181, C_182), k1_zfmisc_1(u1_struct_0(A_180))) | ~m1_subset_1(C_182, u1_struct_0(A_180)) | ~m1_subset_1(B_181, u1_struct_0(A_180)) | ~l1_orders_2(A_180) | ~v3_orders_2(A_180))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.37/1.89  tff(c_44, plain, (![D_55]: (v6_orders_2('#skF_5', '#skF_2') | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_450, plain, (![D_55]: (~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(splitLeft, [status(thm)], [c_44])).
% 4.37/1.89  tff(c_533, plain, (![B_181, C_182]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_181, C_182)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_181, C_182)) | ~v6_orders_2('#skF_1'('#skF_2', B_181, C_182), '#skF_2') | ~r1_orders_2('#skF_2', B_181, C_182) | ~m1_subset_1(C_182, u1_struct_0('#skF_2')) | ~m1_subset_1(B_181, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_529, c_450])).
% 4.37/1.89  tff(c_545, plain, (![B_186, C_187]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_186, C_187)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_186, C_187)) | ~v6_orders_2('#skF_1'('#skF_2', B_186, C_187), '#skF_2') | ~r1_orders_2('#skF_2', B_186, C_187) | ~m1_subset_1(C_187, u1_struct_0('#skF_2')) | ~m1_subset_1(B_186, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_533])).
% 4.37/1.89  tff(c_549, plain, (![B_27, C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, C_33)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_27, C_33)) | ~r1_orders_2('#skF_2', B_27, C_33) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_545])).
% 4.37/1.89  tff(c_560, plain, (![B_188, C_189]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_188, C_189)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_188, C_189)) | ~r1_orders_2('#skF_2', B_188, C_189) | ~m1_subset_1(C_189, u1_struct_0('#skF_2')) | ~m1_subset_1(B_188, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_549])).
% 4.37/1.89  tff(c_564, plain, (![B_27]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, '#skF_3')) | ~r1_orders_2('#skF_2', B_27, '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_560])).
% 4.37/1.89  tff(c_608, plain, (![B_194]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_194, '#skF_3')) | ~r1_orders_2('#skF_2', B_194, '#skF_3') | ~m1_subset_1(B_194, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_564])).
% 4.37/1.89  tff(c_612, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_18, c_608])).
% 4.37/1.89  tff(c_620, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_28, c_30, c_88, c_612])).
% 4.37/1.89  tff(c_621, plain, (v6_orders_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.37/1.89  tff(c_12, plain, (![A_15, C_33, B_27]: (~r1_orders_2(A_15, C_33, B_27) | r2_hidden(C_33, '#skF_1'(A_15, B_27, C_33)) | ~m1_subset_1(C_33, u1_struct_0(A_15)) | ~m1_subset_1(B_27, u1_struct_0(A_15)) | ~l1_orders_2(A_15) | ~v3_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.37/1.89  tff(c_16, plain, (![A_15, C_33, B_27]: (~r1_orders_2(A_15, C_33, B_27) | r2_hidden(B_27, '#skF_1'(A_15, B_27, C_33)) | ~m1_subset_1(C_33, u1_struct_0(A_15)) | ~m1_subset_1(B_27, u1_struct_0(A_15)) | ~l1_orders_2(A_15) | ~v3_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.37/1.89  tff(c_24, plain, (![A_15, C_33, B_27]: (~r1_orders_2(A_15, C_33, B_27) | v6_orders_2('#skF_1'(A_15, B_27, C_33), A_15) | ~m1_subset_1(C_33, u1_struct_0(A_15)) | ~m1_subset_1(B_27, u1_struct_0(A_15)) | ~l1_orders_2(A_15) | ~v3_orders_2(A_15))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.37/1.89  tff(c_373, plain, (![A_139, C_140, B_141]: (~r1_orders_2(A_139, C_140, B_141) | m1_subset_1('#skF_1'(A_139, B_141, C_140), k1_zfmisc_1(u1_struct_0(A_139))) | ~m1_subset_1(C_140, u1_struct_0(A_139)) | ~m1_subset_1(B_141, u1_struct_0(A_139)) | ~l1_orders_2(A_139) | ~v3_orders_2(A_139))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.37/1.89  tff(c_40, plain, (![D_55]: (r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_296, plain, (![D_55]: (~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(splitLeft, [status(thm)], [c_40])).
% 4.37/1.89  tff(c_377, plain, (![B_141, C_140]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_141, C_140)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_141, C_140)) | ~v6_orders_2('#skF_1'('#skF_2', B_141, C_140), '#skF_2') | ~r1_orders_2('#skF_2', C_140, B_141) | ~m1_subset_1(C_140, u1_struct_0('#skF_2')) | ~m1_subset_1(B_141, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_373, c_296])).
% 4.37/1.89  tff(c_389, plain, (![B_145, C_146]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_145, C_146)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_145, C_146)) | ~v6_orders_2('#skF_1'('#skF_2', B_145, C_146), '#skF_2') | ~r1_orders_2('#skF_2', C_146, B_145) | ~m1_subset_1(C_146, u1_struct_0('#skF_2')) | ~m1_subset_1(B_145, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_377])).
% 4.37/1.89  tff(c_393, plain, (![B_27, C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, C_33)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_27, C_33)) | ~r1_orders_2('#skF_2', C_33, B_27) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_389])).
% 4.37/1.89  tff(c_404, plain, (![B_147, C_148]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_147, C_148)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_147, C_148)) | ~r1_orders_2('#skF_2', C_148, B_147) | ~m1_subset_1(C_148, u1_struct_0('#skF_2')) | ~m1_subset_1(B_147, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_393])).
% 4.37/1.89  tff(c_416, plain, (![C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_33)) | ~r1_orders_2('#skF_2', C_33, '#skF_3') | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_404])).
% 4.37/1.89  tff(c_433, plain, (![C_149]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_149)) | ~r1_orders_2('#skF_2', C_149, '#skF_3') | ~m1_subset_1(C_149, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_416])).
% 4.37/1.89  tff(c_441, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_12, c_433])).
% 4.37/1.89  tff(c_448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_28, c_88, c_441])).
% 4.37/1.89  tff(c_449, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_40])).
% 4.37/1.89  tff(c_176, plain, (![A_88, C_89, B_90]: (~r1_orders_2(A_88, C_89, B_90) | m1_subset_1('#skF_1'(A_88, B_90, C_89), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(C_89, u1_struct_0(A_88)) | ~m1_subset_1(B_90, u1_struct_0(A_88)) | ~l1_orders_2(A_88) | ~v3_orders_2(A_88))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.37/1.89  tff(c_38, plain, (![D_55]: (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_99, plain, (![D_55]: (~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(splitLeft, [status(thm)], [c_38])).
% 4.37/1.89  tff(c_180, plain, (![B_90, C_89]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_90, C_89)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_90, C_89)) | ~v6_orders_2('#skF_1'('#skF_2', B_90, C_89), '#skF_2') | ~r1_orders_2('#skF_2', C_89, B_90) | ~m1_subset_1(C_89, u1_struct_0('#skF_2')) | ~m1_subset_1(B_90, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_176, c_99])).
% 4.37/1.89  tff(c_205, plain, (![B_98, C_99]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_98, C_99)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_98, C_99)) | ~v6_orders_2('#skF_1'('#skF_2', B_98, C_99), '#skF_2') | ~r1_orders_2('#skF_2', C_99, B_98) | ~m1_subset_1(C_99, u1_struct_0('#skF_2')) | ~m1_subset_1(B_98, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_180])).
% 4.37/1.89  tff(c_213, plain, (![B_27, C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, C_33)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_27, C_33)) | ~r1_orders_2('#skF_2', C_33, B_27) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_205])).
% 4.37/1.89  tff(c_220, plain, (![B_100, C_101]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_100, C_101)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_100, C_101)) | ~r1_orders_2('#skF_2', C_101, B_100) | ~m1_subset_1(C_101, u1_struct_0('#skF_2')) | ~m1_subset_1(B_100, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_213])).
% 4.37/1.89  tff(c_236, plain, (![C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_33)) | ~r1_orders_2('#skF_2', C_33, '#skF_3') | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_220])).
% 4.37/1.89  tff(c_279, plain, (![C_105]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_105)) | ~r1_orders_2('#skF_2', C_105, '#skF_3') | ~m1_subset_1(C_105, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_236])).
% 4.37/1.89  tff(c_287, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_12, c_279])).
% 4.37/1.89  tff(c_294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_28, c_88, c_287])).
% 4.37/1.89  tff(c_295, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 4.37/1.89  tff(c_702, plain, (![A_225, B_226, C_227]: (~r1_orders_2(A_225, B_226, C_227) | m1_subset_1('#skF_1'(A_225, B_226, C_227), k1_zfmisc_1(u1_struct_0(A_225))) | ~m1_subset_1(C_227, u1_struct_0(A_225)) | ~m1_subset_1(B_226, u1_struct_0(A_225)) | ~l1_orders_2(A_225) | ~v3_orders_2(A_225))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.37/1.89  tff(c_42, plain, (![D_55]: (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_623, plain, (![D_55]: (~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(splitLeft, [status(thm)], [c_42])).
% 4.37/1.89  tff(c_706, plain, (![B_226, C_227]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_226, C_227)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_226, C_227)) | ~v6_orders_2('#skF_1'('#skF_2', B_226, C_227), '#skF_2') | ~r1_orders_2('#skF_2', B_226, C_227) | ~m1_subset_1(C_227, u1_struct_0('#skF_2')) | ~m1_subset_1(B_226, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_702, c_623])).
% 4.37/1.89  tff(c_718, plain, (![B_231, C_232]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_231, C_232)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_231, C_232)) | ~v6_orders_2('#skF_1'('#skF_2', B_231, C_232), '#skF_2') | ~r1_orders_2('#skF_2', B_231, C_232) | ~m1_subset_1(C_232, u1_struct_0('#skF_2')) | ~m1_subset_1(B_231, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_706])).
% 4.37/1.89  tff(c_726, plain, (![B_27, C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, C_33)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_27, C_33)) | ~r1_orders_2('#skF_2', B_27, C_33) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_718])).
% 4.37/1.89  tff(c_733, plain, (![B_233, C_234]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_233, C_234)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_233, C_234)) | ~r1_orders_2('#skF_2', B_233, C_234) | ~m1_subset_1(C_234, u1_struct_0('#skF_2')) | ~m1_subset_1(B_233, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_726])).
% 4.37/1.89  tff(c_745, plain, (![B_27]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, '#skF_3')) | ~r1_orders_2('#skF_2', B_27, '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_733])).
% 4.37/1.89  tff(c_792, plain, (![B_238]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_238, '#skF_3')) | ~r1_orders_2('#skF_2', B_238, '#skF_3') | ~m1_subset_1(B_238, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_745])).
% 4.37/1.89  tff(c_796, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_18, c_792])).
% 4.37/1.89  tff(c_804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_28, c_30, c_88, c_796])).
% 4.37/1.89  tff(c_805, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_42])).
% 4.37/1.89  tff(c_52, plain, (![D_55]: (r2_orders_2('#skF_2', '#skF_3', '#skF_4') | ~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_831, plain, (![D_55]: (r2_orders_2('#skF_2', '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_52])).
% 4.37/1.89  tff(c_833, plain, (![D_243]: (~r2_hidden('#skF_4', D_243) | ~r2_hidden('#skF_3', D_243) | ~m1_subset_1(D_243, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_243, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_86, c_831])).
% 4.37/1.89  tff(c_836, plain, (~r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_3', '#skF_5') | ~v6_orders_2('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_805, c_833])).
% 4.37/1.89  tff(c_840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_621, c_449, c_295, c_836])).
% 4.37/1.89  tff(c_842, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_87])).
% 4.37/1.89  tff(c_56, plain, (r2_hidden('#skF_3', '#skF_5') | r2_orders_2('#skF_2', '#skF_3', '#skF_4') | r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_843, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_842, c_86, c_56])).
% 4.37/1.89  tff(c_841, plain, (v6_orders_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_87])).
% 4.37/1.89  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_orders_2('#skF_2', '#skF_3', '#skF_4') | r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_846, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_842, c_86, c_58])).
% 4.37/1.89  tff(c_54, plain, (r2_hidden('#skF_4', '#skF_5') | r2_orders_2('#skF_2', '#skF_3', '#skF_4') | r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_845, plain, (r2_hidden('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_842, c_86, c_54])).
% 4.37/1.89  tff(c_898, plain, (![A_279, C_280, B_281, D_282]: (r1_orders_2(A_279, C_280, B_281) | r1_orders_2(A_279, B_281, C_280) | ~r2_hidden(C_280, D_282) | ~r2_hidden(B_281, D_282) | ~m1_subset_1(D_282, k1_zfmisc_1(u1_struct_0(A_279))) | ~v6_orders_2(D_282, A_279) | ~m1_subset_1(C_280, u1_struct_0(A_279)) | ~m1_subset_1(B_281, u1_struct_0(A_279)) | ~l1_orders_2(A_279) | ~v3_orders_2(A_279))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.37/1.89  tff(c_917, plain, (![A_283, B_284]: (r1_orders_2(A_283, '#skF_4', B_284) | r1_orders_2(A_283, B_284, '#skF_4') | ~r2_hidden(B_284, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_283))) | ~v6_orders_2('#skF_5', A_283) | ~m1_subset_1('#skF_4', u1_struct_0(A_283)) | ~m1_subset_1(B_284, u1_struct_0(A_283)) | ~l1_orders_2(A_283) | ~v3_orders_2(A_283))), inference(resolution, [status(thm)], [c_845, c_898])).
% 4.37/1.89  tff(c_919, plain, (![B_284]: (r1_orders_2('#skF_2', '#skF_4', B_284) | r1_orders_2('#skF_2', B_284, '#skF_4') | ~r2_hidden(B_284, '#skF_5') | ~v6_orders_2('#skF_5', '#skF_2') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1(B_284, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_846, c_917])).
% 4.37/1.89  tff(c_923, plain, (![B_285]: (r1_orders_2('#skF_2', '#skF_4', B_285) | r1_orders_2('#skF_2', B_285, '#skF_4') | ~r2_hidden(B_285, '#skF_5') | ~m1_subset_1(B_285, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_28, c_841, c_919])).
% 4.37/1.89  tff(c_929, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_3') | r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_923])).
% 4.37/1.89  tff(c_935, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_3') | r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_843, c_929])).
% 4.37/1.89  tff(c_937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_877, c_842, c_935])).
% 4.37/1.89  tff(c_938, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_876])).
% 4.37/1.89  tff(c_939, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_876])).
% 4.37/1.89  tff(c_950, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_938, c_939])).
% 4.37/1.89  tff(c_941, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_938, c_842])).
% 4.37/1.89  tff(c_955, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_950, c_941])).
% 4.37/1.89  tff(c_957, plain, (r2_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_72])).
% 4.37/1.89  tff(c_1400, plain, (![A_414, B_415, C_416]: (r1_orders_2(A_414, B_415, C_416) | ~r2_orders_2(A_414, B_415, C_416) | ~m1_subset_1(C_416, u1_struct_0(A_414)) | ~m1_subset_1(B_415, u1_struct_0(A_414)) | ~l1_orders_2(A_414))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.37/1.89  tff(c_1402, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_957, c_1400])).
% 4.37/1.89  tff(c_1405, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_1402])).
% 4.37/1.89  tff(c_1457, plain, (![A_444, B_445, C_446]: (~r1_orders_2(A_444, B_445, C_446) | m1_subset_1('#skF_1'(A_444, B_445, C_446), k1_zfmisc_1(u1_struct_0(A_444))) | ~m1_subset_1(C_446, u1_struct_0(A_444)) | ~m1_subset_1(B_445, u1_struct_0(A_444)) | ~l1_orders_2(A_444) | ~v3_orders_2(A_444))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.37/1.89  tff(c_956, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 4.37/1.89  tff(c_958, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_956])).
% 4.37/1.89  tff(c_46, plain, (![D_55]: (r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~r2_orders_2('#skF_2', '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_1408, plain, (![D_55]: (r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_957, c_46])).
% 4.37/1.89  tff(c_1409, plain, (![D_55]: (~r2_hidden('#skF_4', D_55) | ~r2_hidden('#skF_3', D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v6_orders_2(D_55, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_958, c_1408])).
% 4.37/1.89  tff(c_1461, plain, (![B_445, C_446]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_445, C_446)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_445, C_446)) | ~v6_orders_2('#skF_1'('#skF_2', B_445, C_446), '#skF_2') | ~r1_orders_2('#skF_2', B_445, C_446) | ~m1_subset_1(C_446, u1_struct_0('#skF_2')) | ~m1_subset_1(B_445, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_1457, c_1409])).
% 4.37/1.89  tff(c_1473, plain, (![B_450, C_451]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_450, C_451)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_450, C_451)) | ~v6_orders_2('#skF_1'('#skF_2', B_450, C_451), '#skF_2') | ~r1_orders_2('#skF_2', B_450, C_451) | ~m1_subset_1(C_451, u1_struct_0('#skF_2')) | ~m1_subset_1(B_450, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1461])).
% 4.37/1.89  tff(c_1477, plain, (![B_27, C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_27, C_33)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_27, C_33)) | ~r1_orders_2('#skF_2', B_27, C_33) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1(B_27, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_1473])).
% 4.37/1.89  tff(c_1507, plain, (![B_456, C_457]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_456, C_457)) | ~r2_hidden('#skF_3', '#skF_1'('#skF_2', B_456, C_457)) | ~r1_orders_2('#skF_2', B_456, C_457) | ~m1_subset_1(C_457, u1_struct_0('#skF_2')) | ~m1_subset_1(B_456, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1477])).
% 4.37/1.89  tff(c_1515, plain, (![C_33]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_33)) | ~r1_orders_2('#skF_2', '#skF_3', C_33) | ~m1_subset_1(C_33, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_1507])).
% 4.37/1.89  tff(c_1551, plain, (![C_459]: (~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_459)) | ~r1_orders_2('#skF_2', '#skF_3', C_459) | ~m1_subset_1(C_459, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_1515])).
% 4.37/1.89  tff(c_1555, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_14, c_1551])).
% 4.37/1.89  tff(c_1563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_28, c_1405, c_1555])).
% 4.37/1.89  tff(c_1565, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_956])).
% 4.37/1.89  tff(c_1586, plain, (![A_463, B_464, C_465]: (r2_orders_2(A_463, B_464, C_465) | C_465=B_464 | ~r1_orders_2(A_463, B_464, C_465) | ~m1_subset_1(C_465, u1_struct_0(A_463)) | ~m1_subset_1(B_464, u1_struct_0(A_463)) | ~l1_orders_2(A_463))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.37/1.89  tff(c_1590, plain, (![B_464]: (r2_orders_2('#skF_2', B_464, '#skF_3') | B_464='#skF_3' | ~r1_orders_2('#skF_2', B_464, '#skF_3') | ~m1_subset_1(B_464, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_1586])).
% 4.37/1.89  tff(c_1610, plain, (![B_470]: (r2_orders_2('#skF_2', B_470, '#skF_3') | B_470='#skF_3' | ~r1_orders_2('#skF_2', B_470, '#skF_3') | ~m1_subset_1(B_470, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1590])).
% 4.37/1.89  tff(c_1613, plain, (r2_orders_2('#skF_2', '#skF_4', '#skF_3') | '#skF_3'='#skF_4' | ~r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_1610])).
% 4.37/1.89  tff(c_1619, plain, (r2_orders_2('#skF_2', '#skF_4', '#skF_3') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1565, c_1613])).
% 4.37/1.89  tff(c_1622, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_1619])).
% 4.37/1.89  tff(c_1629, plain, (r2_orders_2('#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1622, c_957])).
% 4.37/1.89  tff(c_4, plain, (![A_1, C_7]: (~r2_orders_2(A_1, C_7, C_7) | ~m1_subset_1(C_7, u1_struct_0(A_1)) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.37/1.89  tff(c_1641, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_1629, c_4])).
% 4.37/1.89  tff(c_1648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_1641])).
% 4.37/1.89  tff(c_1650, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_1619])).
% 4.37/1.89  tff(c_34, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.37/1.89  tff(c_1579, plain, (![A_460, B_461, C_462]: (r1_orders_2(A_460, B_461, C_462) | ~r2_orders_2(A_460, B_461, C_462) | ~m1_subset_1(C_462, u1_struct_0(A_460)) | ~m1_subset_1(B_461, u1_struct_0(A_460)) | ~l1_orders_2(A_460))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.37/1.89  tff(c_1581, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_957, c_1579])).
% 4.37/1.89  tff(c_1584, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_1581])).
% 4.37/1.89  tff(c_1658, plain, (![C_477, B_478, A_479]: (C_477=B_478 | ~r1_orders_2(A_479, C_477, B_478) | ~r1_orders_2(A_479, B_478, C_477) | ~m1_subset_1(C_477, u1_struct_0(A_479)) | ~m1_subset_1(B_478, u1_struct_0(A_479)) | ~l1_orders_2(A_479) | ~v5_orders_2(A_479))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.37/1.89  tff(c_1660, plain, ('#skF_3'='#skF_4' | ~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_1584, c_1658])).
% 4.37/1.89  tff(c_1665, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_30, c_1565, c_1660])).
% 4.37/1.89  tff(c_1667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1650, c_1665])).
% 4.37/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.89  
% 4.37/1.89  Inference rules
% 4.37/1.89  ----------------------
% 4.37/1.89  #Ref     : 0
% 4.37/1.89  #Sup     : 220
% 4.37/1.89  #Fact    : 0
% 4.37/1.89  #Define  : 0
% 4.37/1.89  #Split   : 24
% 4.37/1.89  #Chain   : 0
% 4.37/1.89  #Close   : 0
% 4.37/1.89  
% 4.37/1.89  Ordering : KBO
% 4.37/1.89  
% 4.37/1.89  Simplification rules
% 4.37/1.89  ----------------------
% 4.37/1.89  #Subsume      : 81
% 4.37/1.89  #Demod        : 513
% 4.37/1.89  #Tautology    : 85
% 4.37/1.89  #SimpNegUnit  : 38
% 4.37/1.89  #BackRed      : 36
% 4.37/1.89  
% 4.37/1.89  #Partial instantiations: 0
% 4.37/1.89  #Strategies tried      : 1
% 4.37/1.89  
% 4.37/1.89  Timing (in seconds)
% 4.37/1.89  ----------------------
% 4.37/1.90  Preprocessing        : 0.36
% 4.37/1.90  Parsing              : 0.19
% 4.37/1.90  CNF conversion       : 0.03
% 4.37/1.90  Main loop            : 0.69
% 4.37/1.90  Inferencing          : 0.29
% 4.37/1.90  Reduction            : 0.19
% 4.37/1.90  Demodulation         : 0.13
% 4.37/1.90  BG Simplification    : 0.03
% 4.37/1.90  Subsumption          : 0.14
% 4.37/1.90  Abstraction          : 0.03
% 4.37/1.90  MUC search           : 0.00
% 4.37/1.90  Cooper               : 0.00
% 4.37/1.90  Total                : 1.13
% 4.37/1.90  Index Insertion      : 0.00
% 4.37/1.90  Index Deletion       : 0.00
% 4.37/1.90  Index Matching       : 0.00
% 4.37/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
