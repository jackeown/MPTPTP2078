%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2025+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:47 EST 2020

% Result     : Theorem 8.69s
% Output     : CNFRefutation 9.05s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 379 expanded)
%              Number of leaves         :   46 ( 159 expanded)
%              Depth                    :   29
%              Number of atoms          :  447 (2077 expanded)
%              Number of equality atoms :   13 ( 131 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_relset_1 > u1_waybel_0 > k2_pre_topc > k1_tops_1 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_236,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & v4_orders_2(C)
                  & v7_waybel_0(C)
                  & l1_waybel_0(C,A) )
               => ( r2_hidden(B,k10_yellow_6(A,C))
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ( D = k2_relset_1(u1_struct_0(C),u1_struct_0(A),u1_waybel_0(A,C))
                       => r2_hidden(B,k2_pre_topc(A,D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_waybel_9)).

tff(f_193,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_159,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = k2_pre_topc(A,B)
              <=> ! [D] :
                    ( r2_hidden(D,u1_struct_0(A))
                   => ( r2_hidden(D,C)
                    <=> ! [E] :
                          ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v3_pre_topc(E,A)
                              & r2_hidden(D,E)
                              & r1_xboole_0(B,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_pre_topc)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_206,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => r1_waybel_0(A,B,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_9)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k10_yellow_6(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).

tff(f_186,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = k10_yellow_6(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_hidden(D,C)
                    <=> ! [E] :
                          ( m1_connsp_2(E,A,D)
                         => r1_waybel_0(A,B,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).

tff(f_153,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C,D] :
              ~ ( r1_waybel_0(A,B,C)
                & r1_waybel_0(A,B,D)
                & r1_xboole_0(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_6)).

tff(c_102,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_100,plain,(
    v2_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_98,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_92,plain,(
    v4_orders_2('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_90,plain,(
    v7_waybel_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_88,plain,(
    l1_waybel_0('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_84,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_114,plain,(
    ! [C_236,B_237,A_238] :
      ( ~ v1_xboole_0(C_236)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(C_236))
      | ~ r2_hidden(A_238,B_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_117,plain,(
    ! [A_238] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_7'))
      | ~ r2_hidden(A_238,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_84,c_114])).

tff(c_118,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_96,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_68,plain,(
    ! [A_194,B_195] :
      ( r2_hidden(A_194,B_195)
      | v1_xboole_0(B_195)
      | ~ m1_subset_1(A_194,B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_80,plain,(
    ~ r2_hidden('#skF_8',k2_pre_topc('#skF_7','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_60,plain,(
    ! [A_178,B_179] :
      ( m1_subset_1(k2_pre_topc(A_178,B_179),k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_518,plain,(
    ! [D_372,A_373,B_374] :
      ( r2_hidden(D_372,'#skF_1'(A_373,B_374,k2_pre_topc(A_373,B_374),D_372))
      | r2_hidden(D_372,k2_pre_topc(A_373,B_374))
      | ~ r2_hidden(D_372,u1_struct_0(A_373))
      | ~ m1_subset_1(k2_pre_topc(A_373,B_374),k1_zfmisc_1(u1_struct_0(A_373)))
      | ~ m1_subset_1(B_374,k1_zfmisc_1(u1_struct_0(A_373)))
      | ~ l1_pre_topc(A_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_521,plain,(
    ! [D_372,A_178,B_179] :
      ( r2_hidden(D_372,'#skF_1'(A_178,B_179,k2_pre_topc(A_178,B_179),D_372))
      | r2_hidden(D_372,k2_pre_topc(A_178,B_179))
      | ~ r2_hidden(D_372,u1_struct_0(A_178))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(resolution,[status(thm)],[c_60,c_518])).

tff(c_62,plain,(
    ! [A_180] :
      ( l1_struct_0(A_180)
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_82,plain,(
    k2_relset_1(u1_struct_0('#skF_9'),u1_struct_0('#skF_7'),u1_waybel_0('#skF_7','#skF_9')) = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_142,plain,(
    ! [A_251,B_252] :
      ( r1_waybel_0(A_251,B_252,k2_relset_1(u1_struct_0(B_252),u1_struct_0(A_251),u1_waybel_0(A_251,B_252)))
      | ~ l1_waybel_0(B_252,A_251)
      | v2_struct_0(B_252)
      | ~ l1_struct_0(A_251)
      | v2_struct_0(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_145,plain,
    ( r1_waybel_0('#skF_7','#skF_9','#skF_10')
    | ~ l1_waybel_0('#skF_9','#skF_7')
    | v2_struct_0('#skF_9')
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_142])).

tff(c_147,plain,
    ( r1_waybel_0('#skF_7','#skF_9','#skF_10')
    | v2_struct_0('#skF_9')
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_145])).

tff(c_148,plain,
    ( r1_waybel_0('#skF_7','#skF_9','#skF_10')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_94,c_147])).

tff(c_149,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_152,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_149])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_152])).

tff(c_158,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_157,plain,(
    r1_waybel_0('#skF_7','#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_58,plain,(
    ! [A_176,B_177] :
      ( m1_subset_1(k10_yellow_6(A_176,B_177),k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_waybel_0(B_177,A_176)
      | ~ v7_waybel_0(B_177)
      | ~ v4_orders_2(B_177)
      | v2_struct_0(B_177)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_86,plain,(
    r2_hidden('#skF_8',k10_yellow_6('#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_32,plain,(
    ! [A_1,B_45,D_78] :
      ( m1_subset_1('#skF_1'(A_1,B_45,k2_pre_topc(A_1,B_45),D_78),k1_zfmisc_1(u1_struct_0(A_1)))
      | r2_hidden(D_78,k2_pre_topc(A_1,B_45))
      | ~ r2_hidden(D_78,u1_struct_0(A_1))
      | ~ m1_subset_1(k2_pre_topc(A_1,B_45),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_506,plain,(
    ! [A_363,B_364,D_365] :
      ( v3_pre_topc('#skF_1'(A_363,B_364,k2_pre_topc(A_363,B_364),D_365),A_363)
      | r2_hidden(D_365,k2_pre_topc(A_363,B_364))
      | ~ r2_hidden(D_365,u1_struct_0(A_363))
      | ~ m1_subset_1(k2_pre_topc(A_363,B_364),k1_zfmisc_1(u1_struct_0(A_363)))
      | ~ m1_subset_1(B_364,k1_zfmisc_1(u1_struct_0(A_363)))
      | ~ l1_pre_topc(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_509,plain,(
    ! [A_178,B_179,D_365] :
      ( v3_pre_topc('#skF_1'(A_178,B_179,k2_pre_topc(A_178,B_179),D_365),A_178)
      | r2_hidden(D_365,k2_pre_topc(A_178,B_179))
      | ~ r2_hidden(D_365,u1_struct_0(A_178))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(resolution,[status(thm)],[c_60,c_506])).

tff(c_552,plain,(
    ! [A_389,B_390,D_391] :
      ( m1_subset_1('#skF_1'(A_389,B_390,k2_pre_topc(A_389,B_390),D_391),k1_zfmisc_1(u1_struct_0(A_389)))
      | r2_hidden(D_391,k2_pre_topc(A_389,B_390))
      | ~ r2_hidden(D_391,u1_struct_0(A_389))
      | ~ m1_subset_1(k2_pre_topc(A_389,B_390),k1_zfmisc_1(u1_struct_0(A_389)))
      | ~ m1_subset_1(B_390,k1_zfmisc_1(u1_struct_0(A_389)))
      | ~ l1_pre_topc(A_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_74,plain,(
    ! [B_207,D_213,C_211,A_199] :
      ( k1_tops_1(B_207,D_213) = D_213
      | ~ v3_pre_topc(D_213,B_207)
      | ~ m1_subset_1(D_213,k1_zfmisc_1(u1_struct_0(B_207)))
      | ~ m1_subset_1(C_211,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(B_207)
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_236,plain,(
    ! [C_270,A_271] :
      ( ~ m1_subset_1(C_270,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271) ) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_245,plain,
    ( ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_84,c_236])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_245])).

tff(c_252,plain,(
    ! [B_207,D_213] :
      ( k1_tops_1(B_207,D_213) = D_213
      | ~ v3_pre_topc(D_213,B_207)
      | ~ m1_subset_1(D_213,k1_zfmisc_1(u1_struct_0(B_207)))
      | ~ l1_pre_topc(B_207) ) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_2306,plain,(
    ! [A_799,B_800,D_801] :
      ( k1_tops_1(A_799,'#skF_1'(A_799,B_800,k2_pre_topc(A_799,B_800),D_801)) = '#skF_1'(A_799,B_800,k2_pre_topc(A_799,B_800),D_801)
      | ~ v3_pre_topc('#skF_1'(A_799,B_800,k2_pre_topc(A_799,B_800),D_801),A_799)
      | r2_hidden(D_801,k2_pre_topc(A_799,B_800))
      | ~ r2_hidden(D_801,u1_struct_0(A_799))
      | ~ m1_subset_1(k2_pre_topc(A_799,B_800),k1_zfmisc_1(u1_struct_0(A_799)))
      | ~ m1_subset_1(B_800,k1_zfmisc_1(u1_struct_0(A_799)))
      | ~ l1_pre_topc(A_799) ) ),
    inference(resolution,[status(thm)],[c_552,c_252])).

tff(c_2310,plain,(
    ! [A_802,B_803,D_804] :
      ( k1_tops_1(A_802,'#skF_1'(A_802,B_803,k2_pre_topc(A_802,B_803),D_804)) = '#skF_1'(A_802,B_803,k2_pre_topc(A_802,B_803),D_804)
      | ~ m1_subset_1(k2_pre_topc(A_802,B_803),k1_zfmisc_1(u1_struct_0(A_802)))
      | r2_hidden(D_804,k2_pre_topc(A_802,B_803))
      | ~ r2_hidden(D_804,u1_struct_0(A_802))
      | ~ m1_subset_1(B_803,k1_zfmisc_1(u1_struct_0(A_802)))
      | ~ l1_pre_topc(A_802) ) ),
    inference(resolution,[status(thm)],[c_509,c_2306])).

tff(c_2314,plain,(
    ! [A_805,B_806,D_807] :
      ( k1_tops_1(A_805,'#skF_1'(A_805,B_806,k2_pre_topc(A_805,B_806),D_807)) = '#skF_1'(A_805,B_806,k2_pre_topc(A_805,B_806),D_807)
      | r2_hidden(D_807,k2_pre_topc(A_805,B_806))
      | ~ r2_hidden(D_807,u1_struct_0(A_805))
      | ~ m1_subset_1(B_806,k1_zfmisc_1(u1_struct_0(A_805)))
      | ~ l1_pre_topc(A_805) ) ),
    inference(resolution,[status(thm)],[c_60,c_2310])).

tff(c_2328,plain,(
    ! [D_807] :
      ( k1_tops_1('#skF_7','#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_807)) = '#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_807)
      | r2_hidden(D_807,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_807,u1_struct_0('#skF_7'))
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_84,c_2314])).

tff(c_2338,plain,(
    ! [D_808] :
      ( k1_tops_1('#skF_7','#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_808)) = '#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_808)
      | r2_hidden(D_808,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_808,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_2328])).

tff(c_54,plain,(
    ! [C_175,A_169,B_173] :
      ( m1_connsp_2(C_175,A_169,B_173)
      | ~ r2_hidden(B_173,k1_tops_1(A_169,C_175))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ m1_subset_1(B_173,u1_struct_0(A_169))
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2343,plain,(
    ! [D_808,B_173] :
      ( m1_connsp_2('#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_808),'#skF_7',B_173)
      | ~ r2_hidden(B_173,'#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_808))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_808),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ m1_subset_1(B_173,u1_struct_0('#skF_7'))
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7')
      | r2_hidden(D_808,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_808,u1_struct_0('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2338,c_54])).

tff(c_2349,plain,(
    ! [D_808,B_173] :
      ( m1_connsp_2('#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_808),'#skF_7',B_173)
      | ~ r2_hidden(B_173,'#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_808))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_808),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ m1_subset_1(B_173,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7')
      | r2_hidden(D_808,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_808,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_2343])).

tff(c_2352,plain,(
    ! [D_809,B_810] :
      ( m1_connsp_2('#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_809),'#skF_7',B_810)
      | ~ r2_hidden(B_810,'#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_809))
      | ~ m1_subset_1('#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_809),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ m1_subset_1(B_810,u1_struct_0('#skF_7'))
      | r2_hidden(D_809,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_809,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_2349])).

tff(c_2355,plain,(
    ! [D_78,B_810] :
      ( m1_connsp_2('#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_78),'#skF_7',B_810)
      | ~ r2_hidden(B_810,'#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_78))
      | ~ m1_subset_1(B_810,u1_struct_0('#skF_7'))
      | r2_hidden(D_78,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_78,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(k2_pre_topc('#skF_7','#skF_10'),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_2352])).

tff(c_2358,plain,(
    ! [D_78,B_810] :
      ( m1_connsp_2('#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_78),'#skF_7',B_810)
      | ~ r2_hidden(B_810,'#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_78))
      | ~ m1_subset_1(B_810,u1_struct_0('#skF_7'))
      | r2_hidden(D_78,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_78,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(k2_pre_topc('#skF_7','#skF_10'),k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_84,c_2355])).

tff(c_2359,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_7','#skF_10'),k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_2358])).

tff(c_2362,plain,
    ( ~ m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_2359])).

tff(c_2366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_84,c_2362])).

tff(c_2682,plain,(
    ! [D_819,B_820] :
      ( m1_connsp_2('#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_819),'#skF_7',B_820)
      | ~ r2_hidden(B_820,'#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_819))
      | ~ m1_subset_1(B_820,u1_struct_0('#skF_7'))
      | r2_hidden(D_819,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_819,u1_struct_0('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_2358])).

tff(c_48,plain,(
    ! [A_85,B_129,E_165,D_162] :
      ( r1_waybel_0(A_85,B_129,E_165)
      | ~ m1_connsp_2(E_165,A_85,D_162)
      | ~ r2_hidden(D_162,k10_yellow_6(A_85,B_129))
      | ~ m1_subset_1(D_162,u1_struct_0(A_85))
      | ~ m1_subset_1(k10_yellow_6(A_85,B_129),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_waybel_0(B_129,A_85)
      | ~ v7_waybel_0(B_129)
      | ~ v4_orders_2(B_129)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2693,plain,(
    ! [B_129,D_819,B_820] :
      ( r1_waybel_0('#skF_7',B_129,'#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_819))
      | ~ r2_hidden(B_820,k10_yellow_6('#skF_7',B_129))
      | ~ m1_subset_1(k10_yellow_6('#skF_7',B_129),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_waybel_0(B_129,'#skF_7')
      | ~ v7_waybel_0(B_129)
      | ~ v4_orders_2(B_129)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ r2_hidden(B_820,'#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_819))
      | ~ m1_subset_1(B_820,u1_struct_0('#skF_7'))
      | r2_hidden(D_819,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_819,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2682,c_48])).

tff(c_2705,plain,(
    ! [B_129,D_819,B_820] :
      ( r1_waybel_0('#skF_7',B_129,'#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_819))
      | ~ r2_hidden(B_820,k10_yellow_6('#skF_7',B_129))
      | ~ m1_subset_1(k10_yellow_6('#skF_7',B_129),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_waybel_0(B_129,'#skF_7')
      | ~ v7_waybel_0(B_129)
      | ~ v4_orders_2(B_129)
      | v2_struct_0(B_129)
      | v2_struct_0('#skF_7')
      | ~ r2_hidden(B_820,'#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_819))
      | ~ m1_subset_1(B_820,u1_struct_0('#skF_7'))
      | r2_hidden(D_819,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_819,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_2693])).

tff(c_3243,plain,(
    ! [B_862,D_863,B_864] :
      ( r1_waybel_0('#skF_7',B_862,'#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_863))
      | ~ r2_hidden(B_864,k10_yellow_6('#skF_7',B_862))
      | ~ m1_subset_1(k10_yellow_6('#skF_7',B_862),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_waybel_0(B_862,'#skF_7')
      | ~ v7_waybel_0(B_862)
      | ~ v4_orders_2(B_862)
      | v2_struct_0(B_862)
      | ~ r2_hidden(B_864,'#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_863))
      | ~ m1_subset_1(B_864,u1_struct_0('#skF_7'))
      | r2_hidden(D_863,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_863,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_2705])).

tff(c_3248,plain,(
    ! [D_863] :
      ( r1_waybel_0('#skF_7','#skF_9','#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_863))
      | ~ m1_subset_1(k10_yellow_6('#skF_7','#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_waybel_0('#skF_9','#skF_7')
      | ~ v7_waybel_0('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ r2_hidden('#skF_8','#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_863))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | r2_hidden(D_863,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_863,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_86,c_3243])).

tff(c_3252,plain,(
    ! [D_863] :
      ( r1_waybel_0('#skF_7','#skF_9','#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_863))
      | ~ m1_subset_1(k10_yellow_6('#skF_7','#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | v2_struct_0('#skF_9')
      | ~ r2_hidden('#skF_8','#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_863))
      | r2_hidden(D_863,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_863,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90,c_88,c_3248])).

tff(c_3253,plain,(
    ! [D_863] :
      ( r1_waybel_0('#skF_7','#skF_9','#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_863))
      | ~ m1_subset_1(k10_yellow_6('#skF_7','#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ r2_hidden('#skF_8','#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_863))
      | r2_hidden(D_863,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_863,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_3252])).

tff(c_3254,plain,(
    ~ m1_subset_1(k10_yellow_6('#skF_7','#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_3253])).

tff(c_3257,plain,
    ( ~ l1_waybel_0('#skF_9','#skF_7')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_3254])).

tff(c_3260,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_92,c_90,c_88,c_3257])).

tff(c_3262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_94,c_3260])).

tff(c_3587,plain,(
    ! [D_876] :
      ( r1_waybel_0('#skF_7','#skF_9','#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_876))
      | ~ r2_hidden('#skF_8','#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_876))
      | r2_hidden(D_876,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_876,u1_struct_0('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_3253])).

tff(c_495,plain,(
    ! [B_357,A_358,D_359] :
      ( r1_xboole_0(B_357,'#skF_1'(A_358,B_357,k2_pre_topc(A_358,B_357),D_359))
      | r2_hidden(D_359,k2_pre_topc(A_358,B_357))
      | ~ r2_hidden(D_359,u1_struct_0(A_358))
      | ~ m1_subset_1(k2_pre_topc(A_358,B_357),k1_zfmisc_1(u1_struct_0(A_358)))
      | ~ m1_subset_1(B_357,k1_zfmisc_1(u1_struct_0(A_358)))
      | ~ l1_pre_topc(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_499,plain,(
    ! [B_360,A_361,D_362] :
      ( r1_xboole_0(B_360,'#skF_1'(A_361,B_360,k2_pre_topc(A_361,B_360),D_362))
      | r2_hidden(D_362,k2_pre_topc(A_361,B_360))
      | ~ r2_hidden(D_362,u1_struct_0(A_361))
      | ~ m1_subset_1(B_360,k1_zfmisc_1(u1_struct_0(A_361)))
      | ~ l1_pre_topc(A_361) ) ),
    inference(resolution,[status(thm)],[c_60,c_495])).

tff(c_66,plain,(
    ! [C_192,D_193,A_183,B_189] :
      ( ~ r1_xboole_0(C_192,D_193)
      | ~ r1_waybel_0(A_183,B_189,D_193)
      | ~ r1_waybel_0(A_183,B_189,C_192)
      | ~ l1_waybel_0(B_189,A_183)
      | ~ v7_waybel_0(B_189)
      | ~ v4_orders_2(B_189)
      | v2_struct_0(B_189)
      | ~ l1_struct_0(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_504,plain,(
    ! [A_361,B_189,D_362,B_360,A_183] :
      ( ~ r1_waybel_0(A_183,B_189,'#skF_1'(A_361,B_360,k2_pre_topc(A_361,B_360),D_362))
      | ~ r1_waybel_0(A_183,B_189,B_360)
      | ~ l1_waybel_0(B_189,A_183)
      | ~ v7_waybel_0(B_189)
      | ~ v4_orders_2(B_189)
      | v2_struct_0(B_189)
      | ~ l1_struct_0(A_183)
      | v2_struct_0(A_183)
      | r2_hidden(D_362,k2_pre_topc(A_361,B_360))
      | ~ r2_hidden(D_362,u1_struct_0(A_361))
      | ~ m1_subset_1(B_360,k1_zfmisc_1(u1_struct_0(A_361)))
      | ~ l1_pre_topc(A_361) ) ),
    inference(resolution,[status(thm)],[c_499,c_66])).

tff(c_3590,plain,(
    ! [D_876] :
      ( ~ r1_waybel_0('#skF_7','#skF_9','#skF_10')
      | ~ l1_waybel_0('#skF_9','#skF_7')
      | ~ v7_waybel_0('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_pre_topc('#skF_7')
      | ~ r2_hidden('#skF_8','#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_876))
      | r2_hidden(D_876,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_876,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_3587,c_504])).

tff(c_3593,plain,(
    ! [D_876] :
      ( v2_struct_0('#skF_9')
      | v2_struct_0('#skF_7')
      | ~ r2_hidden('#skF_8','#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_876))
      | r2_hidden(D_876,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_876,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_84,c_158,c_92,c_90,c_88,c_157,c_3590])).

tff(c_3595,plain,(
    ! [D_877] :
      ( ~ r2_hidden('#skF_8','#skF_1'('#skF_7','#skF_10',k2_pre_topc('#skF_7','#skF_10'),D_877))
      | r2_hidden(D_877,k2_pre_topc('#skF_7','#skF_10'))
      | ~ r2_hidden(D_877,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_94,c_3593])).

tff(c_3599,plain,
    ( r2_hidden('#skF_8',k2_pre_topc('#skF_7','#skF_10'))
    | ~ r2_hidden('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_521,c_3595])).

tff(c_3605,plain,
    ( r2_hidden('#skF_8',k2_pre_topc('#skF_7','#skF_10'))
    | ~ r2_hidden('#skF_8',u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_84,c_3599])).

tff(c_3606,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3605])).

tff(c_3610,plain,
    ( v1_xboole_0(u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_68,c_3606])).

tff(c_3613,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_3610])).

tff(c_3615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_3613])).

tff(c_3617,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_3685,plain,(
    ! [A_900,B_901] :
      ( m1_subset_1(k10_yellow_6(A_900,B_901),k1_zfmisc_1(u1_struct_0(A_900)))
      | ~ l1_waybel_0(B_901,A_900)
      | ~ v7_waybel_0(B_901)
      | ~ v4_orders_2(B_901)
      | v2_struct_0(B_901)
      | ~ l1_pre_topc(A_900)
      | ~ v2_pre_topc(A_900)
      | v2_struct_0(A_900) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_76,plain,(
    ! [C_216,B_215,A_214] :
      ( ~ v1_xboole_0(C_216)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(C_216))
      | ~ r2_hidden(A_214,B_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_3777,plain,(
    ! [A_917,A_918,B_919] :
      ( ~ v1_xboole_0(u1_struct_0(A_917))
      | ~ r2_hidden(A_918,k10_yellow_6(A_917,B_919))
      | ~ l1_waybel_0(B_919,A_917)
      | ~ v7_waybel_0(B_919)
      | ~ v4_orders_2(B_919)
      | v2_struct_0(B_919)
      | ~ l1_pre_topc(A_917)
      | ~ v2_pre_topc(A_917)
      | v2_struct_0(A_917) ) ),
    inference(resolution,[status(thm)],[c_3685,c_76])).

tff(c_3784,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_7'))
    | ~ l1_waybel_0('#skF_9','#skF_7')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_86,c_3777])).

tff(c_3788,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_92,c_90,c_88,c_3617,c_3784])).

tff(c_3790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_94,c_3788])).

%------------------------------------------------------------------------------
