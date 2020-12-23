%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2025+1.003 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 11.27s
% Output     : CNFRefutation 11.27s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 380 expanded)
%              Number of leaves         :   47 ( 160 expanded)
%              Depth                    :   29
%              Number of atoms          :  447 (2077 expanded)
%              Number of equality atoms :   13 ( 131 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_relset_1 > u1_waybel_0 > k2_pre_topc > k1_tops_1 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_11 > #skF_6 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_7 > #skF_1

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

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

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

tff(f_252,negated_conjecture,(
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

tff(f_209,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_181,axiom,(
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

tff(f_222,axiom,(
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

tff(f_202,axiom,(
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

tff(f_175,axiom,(
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
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_100,plain,(
    v2_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_98,plain,(
    l1_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_92,plain,(
    v4_orders_2('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_90,plain,(
    v7_waybel_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_88,plain,(
    l1_waybel_0('#skF_10','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_84,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_113,plain,(
    ! [C_236,B_237,A_238] :
      ( ~ v1_xboole_0(C_236)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(C_236))
      | ~ r2_hidden(A_238,B_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_116,plain,(
    ! [A_238] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_238,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_84,c_113])).

tff(c_121,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_96,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_70,plain,(
    ! [A_199,B_200] :
      ( r2_hidden(A_199,B_200)
      | v1_xboole_0(B_200)
      | ~ m1_subset_1(A_199,B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_80,plain,(
    ~ r2_hidden('#skF_9',k2_pre_topc('#skF_8','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_60,plain,(
    ! [A_178,B_179] :
      ( m1_subset_1(k2_pre_topc(A_178,B_179),k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_526,plain,(
    ! [D_369,A_370,B_371] :
      ( r2_hidden(D_369,'#skF_1'(A_370,B_371,k2_pre_topc(A_370,B_371),D_369))
      | r2_hidden(D_369,k2_pre_topc(A_370,B_371))
      | ~ r2_hidden(D_369,u1_struct_0(A_370))
      | ~ m1_subset_1(k2_pre_topc(A_370,B_371),k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ m1_subset_1(B_371,k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ l1_pre_topc(A_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_529,plain,(
    ! [D_369,A_178,B_179] :
      ( r2_hidden(D_369,'#skF_1'(A_178,B_179,k2_pre_topc(A_178,B_179),D_369))
      | r2_hidden(D_369,k2_pre_topc(A_178,B_179))
      | ~ r2_hidden(D_369,u1_struct_0(A_178))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(resolution,[status(thm)],[c_60,c_526])).

tff(c_62,plain,(
    ! [A_180] :
      ( l1_struct_0(A_180)
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_82,plain,(
    k2_relset_1(u1_struct_0('#skF_10'),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8','#skF_10')) = '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_143,plain,(
    ! [A_254,B_255] :
      ( r1_waybel_0(A_254,B_255,k2_relset_1(u1_struct_0(B_255),u1_struct_0(A_254),u1_waybel_0(A_254,B_255)))
      | ~ l1_waybel_0(B_255,A_254)
      | v2_struct_0(B_255)
      | ~ l1_struct_0(A_254)
      | v2_struct_0(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_146,plain,
    ( r1_waybel_0('#skF_8','#skF_10','#skF_11')
    | ~ l1_waybel_0('#skF_10','#skF_8')
    | v2_struct_0('#skF_10')
    | ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_143])).

tff(c_148,plain,
    ( r1_waybel_0('#skF_8','#skF_10','#skF_11')
    | v2_struct_0('#skF_10')
    | ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_146])).

tff(c_149,plain,
    ( r1_waybel_0('#skF_8','#skF_10','#skF_11')
    | ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_94,c_148])).

tff(c_150,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_153,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_150])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_153])).

tff(c_159,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_158,plain,(
    r1_waybel_0('#skF_8','#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_149])).

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
    r2_hidden('#skF_9',k10_yellow_6('#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_32,plain,(
    ! [A_1,B_45,D_78] :
      ( m1_subset_1('#skF_1'(A_1,B_45,k2_pre_topc(A_1,B_45),D_78),k1_zfmisc_1(u1_struct_0(A_1)))
      | r2_hidden(D_78,k2_pre_topc(A_1,B_45))
      | ~ r2_hidden(D_78,u1_struct_0(A_1))
      | ~ m1_subset_1(k2_pre_topc(A_1,B_45),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_517,plain,(
    ! [A_360,B_361,D_362] :
      ( v3_pre_topc('#skF_1'(A_360,B_361,k2_pre_topc(A_360,B_361),D_362),A_360)
      | r2_hidden(D_362,k2_pre_topc(A_360,B_361))
      | ~ r2_hidden(D_362,u1_struct_0(A_360))
      | ~ m1_subset_1(k2_pre_topc(A_360,B_361),k1_zfmisc_1(u1_struct_0(A_360)))
      | ~ m1_subset_1(B_361,k1_zfmisc_1(u1_struct_0(A_360)))
      | ~ l1_pre_topc(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_520,plain,(
    ! [A_178,B_179,D_362] :
      ( v3_pre_topc('#skF_1'(A_178,B_179,k2_pre_topc(A_178,B_179),D_362),A_178)
      | r2_hidden(D_362,k2_pre_topc(A_178,B_179))
      | ~ r2_hidden(D_362,u1_struct_0(A_178))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(resolution,[status(thm)],[c_60,c_517])).

tff(c_583,plain,(
    ! [A_389,B_390,D_391] :
      ( m1_subset_1('#skF_1'(A_389,B_390,k2_pre_topc(A_389,B_390),D_391),k1_zfmisc_1(u1_struct_0(A_389)))
      | r2_hidden(D_391,k2_pre_topc(A_389,B_390))
      | ~ r2_hidden(D_391,u1_struct_0(A_389))
      | ~ m1_subset_1(k2_pre_topc(A_389,B_390),k1_zfmisc_1(u1_struct_0(A_389)))
      | ~ m1_subset_1(B_390,k1_zfmisc_1(u1_struct_0(A_389)))
      | ~ l1_pre_topc(A_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_74,plain,(
    ! [B_209,D_215,C_213,A_201] :
      ( k1_tops_1(B_209,D_215) = D_215
      | ~ v3_pre_topc(D_215,B_209)
      | ~ m1_subset_1(D_215,k1_zfmisc_1(u1_struct_0(B_209)))
      | ~ m1_subset_1(C_213,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_pre_topc(B_209)
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_187,plain,(
    ! [C_264,A_265] :
      ( ~ m1_subset_1(C_264,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265)
      | ~ v2_pre_topc(A_265) ) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_199,plain,
    ( ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_187])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_199])).

tff(c_207,plain,(
    ! [B_209,D_215] :
      ( k1_tops_1(B_209,D_215) = D_215
      | ~ v3_pre_topc(D_215,B_209)
      | ~ m1_subset_1(D_215,k1_zfmisc_1(u1_struct_0(B_209)))
      | ~ l1_pre_topc(B_209) ) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_3965,plain,(
    ! [A_1122,B_1123,D_1124] :
      ( k1_tops_1(A_1122,'#skF_1'(A_1122,B_1123,k2_pre_topc(A_1122,B_1123),D_1124)) = '#skF_1'(A_1122,B_1123,k2_pre_topc(A_1122,B_1123),D_1124)
      | ~ v3_pre_topc('#skF_1'(A_1122,B_1123,k2_pre_topc(A_1122,B_1123),D_1124),A_1122)
      | r2_hidden(D_1124,k2_pre_topc(A_1122,B_1123))
      | ~ r2_hidden(D_1124,u1_struct_0(A_1122))
      | ~ m1_subset_1(k2_pre_topc(A_1122,B_1123),k1_zfmisc_1(u1_struct_0(A_1122)))
      | ~ m1_subset_1(B_1123,k1_zfmisc_1(u1_struct_0(A_1122)))
      | ~ l1_pre_topc(A_1122) ) ),
    inference(resolution,[status(thm)],[c_583,c_207])).

tff(c_3969,plain,(
    ! [A_1125,B_1126,D_1127] :
      ( k1_tops_1(A_1125,'#skF_1'(A_1125,B_1126,k2_pre_topc(A_1125,B_1126),D_1127)) = '#skF_1'(A_1125,B_1126,k2_pre_topc(A_1125,B_1126),D_1127)
      | ~ m1_subset_1(k2_pre_topc(A_1125,B_1126),k1_zfmisc_1(u1_struct_0(A_1125)))
      | r2_hidden(D_1127,k2_pre_topc(A_1125,B_1126))
      | ~ r2_hidden(D_1127,u1_struct_0(A_1125))
      | ~ m1_subset_1(B_1126,k1_zfmisc_1(u1_struct_0(A_1125)))
      | ~ l1_pre_topc(A_1125) ) ),
    inference(resolution,[status(thm)],[c_520,c_3965])).

tff(c_3973,plain,(
    ! [A_1128,B_1129,D_1130] :
      ( k1_tops_1(A_1128,'#skF_1'(A_1128,B_1129,k2_pre_topc(A_1128,B_1129),D_1130)) = '#skF_1'(A_1128,B_1129,k2_pre_topc(A_1128,B_1129),D_1130)
      | r2_hidden(D_1130,k2_pre_topc(A_1128,B_1129))
      | ~ r2_hidden(D_1130,u1_struct_0(A_1128))
      | ~ m1_subset_1(B_1129,k1_zfmisc_1(u1_struct_0(A_1128)))
      | ~ l1_pre_topc(A_1128) ) ),
    inference(resolution,[status(thm)],[c_60,c_3969])).

tff(c_3991,plain,(
    ! [D_1130] :
      ( k1_tops_1('#skF_8','#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1130)) = '#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1130)
      | r2_hidden(D_1130,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1130,u1_struct_0('#skF_8'))
      | ~ l1_pre_topc('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_84,c_3973])).

tff(c_4003,plain,(
    ! [D_1131] :
      ( k1_tops_1('#skF_8','#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1131)) = '#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1131)
      | r2_hidden(D_1131,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1131,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_3991])).

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

tff(c_4008,plain,(
    ! [D_1131,B_173] :
      ( m1_connsp_2('#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1131),'#skF_8',B_173)
      | ~ r2_hidden(B_173,'#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1131))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1131),k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ m1_subset_1(B_173,u1_struct_0('#skF_8'))
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8')
      | r2_hidden(D_1131,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1131,u1_struct_0('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4003,c_54])).

tff(c_4014,plain,(
    ! [D_1131,B_173] :
      ( m1_connsp_2('#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1131),'#skF_8',B_173)
      | ~ r2_hidden(B_173,'#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1131))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1131),k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ m1_subset_1(B_173,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8')
      | r2_hidden(D_1131,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1131,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_4008])).

tff(c_4017,plain,(
    ! [D_1132,B_1133] :
      ( m1_connsp_2('#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1132),'#skF_8',B_1133)
      | ~ r2_hidden(B_1133,'#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1132))
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1132),k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ m1_subset_1(B_1133,u1_struct_0('#skF_8'))
      | r2_hidden(D_1132,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1132,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_4014])).

tff(c_4020,plain,(
    ! [D_78,B_1133] :
      ( m1_connsp_2('#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_78),'#skF_8',B_1133)
      | ~ r2_hidden(B_1133,'#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_78))
      | ~ m1_subset_1(B_1133,u1_struct_0('#skF_8'))
      | r2_hidden(D_78,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_78,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(k2_pre_topc('#skF_8','#skF_11'),k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ m1_subset_1('#skF_11',k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_pre_topc('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_32,c_4017])).

tff(c_4023,plain,(
    ! [D_78,B_1133] :
      ( m1_connsp_2('#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_78),'#skF_8',B_1133)
      | ~ r2_hidden(B_1133,'#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_78))
      | ~ m1_subset_1(B_1133,u1_struct_0('#skF_8'))
      | r2_hidden(D_78,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_78,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(k2_pre_topc('#skF_8','#skF_11'),k1_zfmisc_1(u1_struct_0('#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_84,c_4020])).

tff(c_4024,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_8','#skF_11'),k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_4023])).

tff(c_4027,plain,
    ( ~ m1_subset_1('#skF_11',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_4024])).

tff(c_4031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_84,c_4027])).

tff(c_4480,plain,(
    ! [D_1138,B_1139] :
      ( m1_connsp_2('#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1138),'#skF_8',B_1139)
      | ~ r2_hidden(B_1139,'#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1138))
      | ~ m1_subset_1(B_1139,u1_struct_0('#skF_8'))
      | r2_hidden(D_1138,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1138,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_4023])).

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

tff(c_4488,plain,(
    ! [B_129,D_1138,B_1139] :
      ( r1_waybel_0('#skF_8',B_129,'#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1138))
      | ~ r2_hidden(B_1139,k10_yellow_6('#skF_8',B_129))
      | ~ m1_subset_1(k10_yellow_6('#skF_8',B_129),k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_waybel_0(B_129,'#skF_8')
      | ~ v7_waybel_0(B_129)
      | ~ v4_orders_2(B_129)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ r2_hidden(B_1139,'#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1138))
      | ~ m1_subset_1(B_1139,u1_struct_0('#skF_8'))
      | r2_hidden(D_1138,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1138,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_4480,c_48])).

tff(c_4501,plain,(
    ! [B_129,D_1138,B_1139] :
      ( r1_waybel_0('#skF_8',B_129,'#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1138))
      | ~ r2_hidden(B_1139,k10_yellow_6('#skF_8',B_129))
      | ~ m1_subset_1(k10_yellow_6('#skF_8',B_129),k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_waybel_0(B_129,'#skF_8')
      | ~ v7_waybel_0(B_129)
      | ~ v4_orders_2(B_129)
      | v2_struct_0(B_129)
      | v2_struct_0('#skF_8')
      | ~ r2_hidden(B_1139,'#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1138))
      | ~ m1_subset_1(B_1139,u1_struct_0('#skF_8'))
      | r2_hidden(D_1138,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1138,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_4488])).

tff(c_5864,plain,(
    ! [B_1207,D_1208,B_1209] :
      ( r1_waybel_0('#skF_8',B_1207,'#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1208))
      | ~ r2_hidden(B_1209,k10_yellow_6('#skF_8',B_1207))
      | ~ m1_subset_1(k10_yellow_6('#skF_8',B_1207),k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_waybel_0(B_1207,'#skF_8')
      | ~ v7_waybel_0(B_1207)
      | ~ v4_orders_2(B_1207)
      | v2_struct_0(B_1207)
      | ~ r2_hidden(B_1209,'#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1208))
      | ~ m1_subset_1(B_1209,u1_struct_0('#skF_8'))
      | r2_hidden(D_1208,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1208,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_4501])).

tff(c_5872,plain,(
    ! [D_1208] :
      ( r1_waybel_0('#skF_8','#skF_10','#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1208))
      | ~ m1_subset_1(k10_yellow_6('#skF_8','#skF_10'),k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_waybel_0('#skF_10','#skF_8')
      | ~ v7_waybel_0('#skF_10')
      | ~ v4_orders_2('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ r2_hidden('#skF_9','#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1208))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
      | r2_hidden(D_1208,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1208,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_86,c_5864])).

tff(c_5877,plain,(
    ! [D_1208] :
      ( r1_waybel_0('#skF_8','#skF_10','#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1208))
      | ~ m1_subset_1(k10_yellow_6('#skF_8','#skF_10'),k1_zfmisc_1(u1_struct_0('#skF_8')))
      | v2_struct_0('#skF_10')
      | ~ r2_hidden('#skF_9','#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1208))
      | r2_hidden(D_1208,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1208,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90,c_88,c_5872])).

tff(c_5878,plain,(
    ! [D_1208] :
      ( r1_waybel_0('#skF_8','#skF_10','#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1208))
      | ~ m1_subset_1(k10_yellow_6('#skF_8','#skF_10'),k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r2_hidden('#skF_9','#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1208))
      | r2_hidden(D_1208,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1208,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_5877])).

tff(c_5879,plain,(
    ~ m1_subset_1(k10_yellow_6('#skF_8','#skF_10'),k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_5878])).

tff(c_5882,plain,
    ( ~ l1_waybel_0('#skF_10','#skF_8')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_5879])).

tff(c_5885,plain,
    ( v2_struct_0('#skF_10')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_92,c_90,c_88,c_5882])).

tff(c_5887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_94,c_5885])).

tff(c_5888,plain,(
    ! [D_1208] :
      ( r1_waybel_0('#skF_8','#skF_10','#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1208))
      | ~ r2_hidden('#skF_9','#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1208))
      | r2_hidden(D_1208,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1208,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_5878])).

tff(c_522,plain,(
    ! [B_366,A_367,D_368] :
      ( r1_xboole_0(B_366,'#skF_1'(A_367,B_366,k2_pre_topc(A_367,B_366),D_368))
      | r2_hidden(D_368,k2_pre_topc(A_367,B_366))
      | ~ r2_hidden(D_368,u1_struct_0(A_367))
      | ~ m1_subset_1(k2_pre_topc(A_367,B_366),k1_zfmisc_1(u1_struct_0(A_367)))
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0(A_367)))
      | ~ l1_pre_topc(A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_530,plain,(
    ! [B_372,A_373,D_374] :
      ( r1_xboole_0(B_372,'#skF_1'(A_373,B_372,k2_pre_topc(A_373,B_372),D_374))
      | r2_hidden(D_374,k2_pre_topc(A_373,B_372))
      | ~ r2_hidden(D_374,u1_struct_0(A_373))
      | ~ m1_subset_1(B_372,k1_zfmisc_1(u1_struct_0(A_373)))
      | ~ l1_pre_topc(A_373) ) ),
    inference(resolution,[status(thm)],[c_60,c_522])).

tff(c_68,plain,(
    ! [C_197,D_198,A_188,B_194] :
      ( ~ r1_xboole_0(C_197,D_198)
      | ~ r1_waybel_0(A_188,B_194,D_198)
      | ~ r1_waybel_0(A_188,B_194,C_197)
      | ~ l1_waybel_0(B_194,A_188)
      | ~ v7_waybel_0(B_194)
      | ~ v4_orders_2(B_194)
      | v2_struct_0(B_194)
      | ~ l1_struct_0(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_6853,plain,(
    ! [D_1223,B_1219,A_1222,B_1220,A_1221] :
      ( ~ r1_waybel_0(A_1221,B_1219,'#skF_1'(A_1222,B_1220,k2_pre_topc(A_1222,B_1220),D_1223))
      | ~ r1_waybel_0(A_1221,B_1219,B_1220)
      | ~ l1_waybel_0(B_1219,A_1221)
      | ~ v7_waybel_0(B_1219)
      | ~ v4_orders_2(B_1219)
      | v2_struct_0(B_1219)
      | ~ l1_struct_0(A_1221)
      | v2_struct_0(A_1221)
      | r2_hidden(D_1223,k2_pre_topc(A_1222,B_1220))
      | ~ r2_hidden(D_1223,u1_struct_0(A_1222))
      | ~ m1_subset_1(B_1220,k1_zfmisc_1(u1_struct_0(A_1222)))
      | ~ l1_pre_topc(A_1222) ) ),
    inference(resolution,[status(thm)],[c_530,c_68])).

tff(c_6856,plain,(
    ! [D_1208] :
      ( ~ r1_waybel_0('#skF_8','#skF_10','#skF_11')
      | ~ l1_waybel_0('#skF_10','#skF_8')
      | ~ v7_waybel_0('#skF_10')
      | ~ v4_orders_2('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_struct_0('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1('#skF_11',k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_pre_topc('#skF_8')
      | ~ r2_hidden('#skF_9','#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1208))
      | r2_hidden(D_1208,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1208,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_5888,c_6853])).

tff(c_6859,plain,(
    ! [D_1208] :
      ( v2_struct_0('#skF_10')
      | v2_struct_0('#skF_8')
      | ~ r2_hidden('#skF_9','#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1208))
      | r2_hidden(D_1208,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1208,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_84,c_159,c_92,c_90,c_88,c_158,c_6856])).

tff(c_6861,plain,(
    ! [D_1224] :
      ( ~ r2_hidden('#skF_9','#skF_1'('#skF_8','#skF_11',k2_pre_topc('#skF_8','#skF_11'),D_1224))
      | r2_hidden(D_1224,k2_pre_topc('#skF_8','#skF_11'))
      | ~ r2_hidden(D_1224,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_94,c_6859])).

tff(c_6865,plain,
    ( r2_hidden('#skF_9',k2_pre_topc('#skF_8','#skF_11'))
    | ~ r2_hidden('#skF_9',u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_11',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_529,c_6861])).

tff(c_6871,plain,
    ( r2_hidden('#skF_9',k2_pre_topc('#skF_8','#skF_11'))
    | ~ r2_hidden('#skF_9',u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_84,c_6865])).

tff(c_6872,plain,(
    ~ r2_hidden('#skF_9',u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_6871])).

tff(c_6876,plain,
    ( v1_xboole_0(u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_70,c_6872])).

tff(c_6879,plain,(
    v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_6876])).

tff(c_6881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_6879])).

tff(c_6883,plain,(
    v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_6930,plain,(
    ! [A_1242,B_1243] :
      ( m1_subset_1(k10_yellow_6(A_1242,B_1243),k1_zfmisc_1(u1_struct_0(A_1242)))
      | ~ l1_waybel_0(B_1243,A_1242)
      | ~ v7_waybel_0(B_1243)
      | ~ v4_orders_2(B_1243)
      | v2_struct_0(B_1243)
      | ~ l1_pre_topc(A_1242)
      | ~ v2_pre_topc(A_1242)
      | v2_struct_0(A_1242) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_76,plain,(
    ! [C_218,B_217,A_216] :
      ( ~ v1_xboole_0(C_218)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(C_218))
      | ~ r2_hidden(A_216,B_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_7063,plain,(
    ! [A_1270,A_1271,B_1272] :
      ( ~ v1_xboole_0(u1_struct_0(A_1270))
      | ~ r2_hidden(A_1271,k10_yellow_6(A_1270,B_1272))
      | ~ l1_waybel_0(B_1272,A_1270)
      | ~ v7_waybel_0(B_1272)
      | ~ v4_orders_2(B_1272)
      | v2_struct_0(B_1272)
      | ~ l1_pre_topc(A_1270)
      | ~ v2_pre_topc(A_1270)
      | v2_struct_0(A_1270) ) ),
    inference(resolution,[status(thm)],[c_6930,c_76])).

tff(c_7070,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_8'))
    | ~ l1_waybel_0('#skF_10','#skF_8')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_86,c_7063])).

tff(c_7074,plain,
    ( v2_struct_0('#skF_10')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_92,c_90,c_88,c_6883,c_7070])).

tff(c_7076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_94,c_7074])).

%------------------------------------------------------------------------------
