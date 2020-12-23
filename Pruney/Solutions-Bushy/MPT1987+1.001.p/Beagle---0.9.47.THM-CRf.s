%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1987+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:45 EST 2020

% Result     : Theorem 5.58s
% Output     : CNFRefutation 5.99s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 705 expanded)
%              Number of leaves         :   44 ( 290 expanded)
%              Depth                    :   45
%              Number of atoms          : 1062 (5693 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_waybel_3 > r1_orders_2 > v1_waybel_7 > v1_waybel_0 > v12_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v3_lattice3 > v2_waybel_1 > v2_struct_0 > v2_lattice3 > v25_waybel_0 > v24_waybel_0 > v1_xboole_0 > v1_lattice3 > l1_orders_2 > k2_yellow_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_waybel_7,type,(
    v1_waybel_7: ( $i * $i ) > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

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

tff(v3_lattice3,type,(
    v3_lattice3: $i > $o )).

tff(v2_waybel_1,type,(
    v2_waybel_1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v12_waybel_0,type,(
    v12_waybel_0: ( $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v25_waybel_0,type,(
    v25_waybel_0: $i > $o )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r1_waybel_3,type,(
    r1_waybel_3: ( $i * $i * $i ) > $o )).

tff(v24_waybel_0,type,(
    v24_waybel_0: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_264,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v2_waybel_1(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & v3_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r1_waybel_3(A,B,C)
                <=> ! [D] :
                      ( ( ~ v1_xboole_0(D)
                        & v1_waybel_0(D,A)
                        & v12_waybel_0(D,A)
                        & v1_waybel_7(D,A)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                     => ( r3_orders_2(A,C,k1_yellow_0(A,D))
                       => r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_waybel_7)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v3_lattice3(A) )
       => ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v24_waybel_0(A)
          & v25_waybel_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc11_waybel_0)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v24_waybel_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & v1_waybel_0(D,A)
                      & v12_waybel_0(D,A)
                      & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                   => ( r3_orders_2(A,C,k1_yellow_0(A,D))
                     => r2_hidden(B,D) ) )
               => r1_waybel_3(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_3)).

tff(f_202,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_waybel_1(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_waybel_0(B,A)
            & v12_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( ~ r2_hidden(C,B)
                  & ! [D] :
                      ( ( ~ v1_xboole_0(D)
                        & v1_waybel_0(D,A)
                        & v12_waybel_0(D,A)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                     => ~ ( v1_waybel_7(D,A)
                          & r1_tarski(B,D)
                          & ~ r2_hidden(C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_waybel_7)).

tff(f_53,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_223,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v3_lattice3(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ( r3_orders_2(A,k1_yellow_0(A,B),k1_yellow_0(A,C))
            & r1_orders_2(A,k2_yellow_0(A,C),k2_yellow_0(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_7)).

tff(f_153,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_orders_2(A,B,C)
                      & r1_orders_2(A,C,D) )
                   => r1_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_waybel_3(A,B,C)
               => ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & v1_waybel_0(D,A)
                      & v12_waybel_0(D,A)
                      & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                   => ( r3_orders_2(A,C,k1_yellow_0(A,D))
                     => r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_3)).

tff(c_56,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_60,plain,(
    v2_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_58,plain,(
    v3_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_70,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_106,plain,(
    ! [A_93] :
      ( v24_waybel_0(A_93)
      | ~ v3_lattice3(A_93)
      | ~ v3_orders_2(A_93)
      | v2_struct_0(A_93)
      | ~ l1_orders_2(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_109,plain,
    ( v24_waybel_0('#skF_3')
    | ~ v3_lattice3('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_106])).

tff(c_112,plain,
    ( v24_waybel_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_109])).

tff(c_113,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_10,plain,(
    ! [A_2] :
      ( ~ v2_struct_0(A_2)
      | ~ v2_lattice3(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_116,plain,
    ( ~ v2_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_113,c_10])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_116])).

tff(c_122,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_84,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ r1_waybel_3('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_104,plain,(
    ~ r1_waybel_3('#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_68,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_66,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_121,plain,(
    v24_waybel_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_26,plain,(
    ! [A_23,B_31,C_35] :
      ( v12_waybel_0('#skF_1'(A_23,B_31,C_35),A_23)
      | r1_waybel_3(A_23,B_31,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_23))
      | ~ m1_subset_1(B_31,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v24_waybel_0(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_28,plain,(
    ! [A_23,B_31,C_35] :
      ( v1_waybel_0('#skF_1'(A_23,B_31,C_35),A_23)
      | r1_waybel_3(A_23,B_31,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_23))
      | ~ m1_subset_1(B_31,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v24_waybel_0(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_24,plain,(
    ! [A_23,B_31,C_35] :
      ( m1_subset_1('#skF_1'(A_23,B_31,C_35),k1_zfmisc_1(u1_struct_0(A_23)))
      | r1_waybel_3(A_23,B_31,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_23))
      | ~ m1_subset_1(B_31,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v24_waybel_0(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_64,plain,(
    v2_waybel_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_62,plain,(
    v1_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_245,plain,(
    ! [A_149,B_150,C_151] :
      ( v12_waybel_0('#skF_2'(A_149,B_150,C_151),A_149)
      | r2_hidden(C_151,B_150)
      | ~ m1_subset_1(C_151,u1_struct_0(A_149))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ v12_waybel_0(B_150,A_149)
      | ~ v1_waybel_0(B_150,A_149)
      | v1_xboole_0(B_150)
      | ~ l1_orders_2(A_149)
      | ~ v2_lattice3(A_149)
      | ~ v1_lattice3(A_149)
      | ~ v2_waybel_1(A_149)
      | ~ v5_orders_2(A_149)
      | ~ v4_orders_2(A_149)
      | ~ v3_orders_2(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_248,plain,(
    ! [A_23,B_31,C_35,C_151] :
      ( v12_waybel_0('#skF_2'(A_23,'#skF_1'(A_23,B_31,C_35),C_151),A_23)
      | r2_hidden(C_151,'#skF_1'(A_23,B_31,C_35))
      | ~ m1_subset_1(C_151,u1_struct_0(A_23))
      | ~ v12_waybel_0('#skF_1'(A_23,B_31,C_35),A_23)
      | ~ v1_waybel_0('#skF_1'(A_23,B_31,C_35),A_23)
      | v1_xboole_0('#skF_1'(A_23,B_31,C_35))
      | ~ v2_lattice3(A_23)
      | ~ v1_lattice3(A_23)
      | ~ v2_waybel_1(A_23)
      | r1_waybel_3(A_23,B_31,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_23))
      | ~ m1_subset_1(B_31,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v24_waybel_0(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_24,c_245])).

tff(c_266,plain,(
    ! [A_155,B_156,C_157] :
      ( v1_waybel_0('#skF_2'(A_155,B_156,C_157),A_155)
      | r2_hidden(C_157,B_156)
      | ~ m1_subset_1(C_157,u1_struct_0(A_155))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ v12_waybel_0(B_156,A_155)
      | ~ v1_waybel_0(B_156,A_155)
      | v1_xboole_0(B_156)
      | ~ l1_orders_2(A_155)
      | ~ v2_lattice3(A_155)
      | ~ v1_lattice3(A_155)
      | ~ v2_waybel_1(A_155)
      | ~ v5_orders_2(A_155)
      | ~ v4_orders_2(A_155)
      | ~ v3_orders_2(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_269,plain,(
    ! [A_23,B_31,C_35,C_157] :
      ( v1_waybel_0('#skF_2'(A_23,'#skF_1'(A_23,B_31,C_35),C_157),A_23)
      | r2_hidden(C_157,'#skF_1'(A_23,B_31,C_35))
      | ~ m1_subset_1(C_157,u1_struct_0(A_23))
      | ~ v12_waybel_0('#skF_1'(A_23,B_31,C_35),A_23)
      | ~ v1_waybel_0('#skF_1'(A_23,B_31,C_35),A_23)
      | v1_xboole_0('#skF_1'(A_23,B_31,C_35))
      | ~ v2_lattice3(A_23)
      | ~ v1_lattice3(A_23)
      | ~ v2_waybel_1(A_23)
      | r1_waybel_3(A_23,B_31,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_23))
      | ~ m1_subset_1(B_31,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v24_waybel_0(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_24,c_266])).

tff(c_236,plain,(
    ! [A_140,B_141,C_142] :
      ( v1_waybel_7('#skF_2'(A_140,B_141,C_142),A_140)
      | r2_hidden(C_142,B_141)
      | ~ m1_subset_1(C_142,u1_struct_0(A_140))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ v12_waybel_0(B_141,A_140)
      | ~ v1_waybel_0(B_141,A_140)
      | v1_xboole_0(B_141)
      | ~ l1_orders_2(A_140)
      | ~ v2_lattice3(A_140)
      | ~ v1_lattice3(A_140)
      | ~ v2_waybel_1(A_140)
      | ~ v5_orders_2(A_140)
      | ~ v4_orders_2(A_140)
      | ~ v3_orders_2(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_239,plain,(
    ! [A_23,B_31,C_35,C_142] :
      ( v1_waybel_7('#skF_2'(A_23,'#skF_1'(A_23,B_31,C_35),C_142),A_23)
      | r2_hidden(C_142,'#skF_1'(A_23,B_31,C_35))
      | ~ m1_subset_1(C_142,u1_struct_0(A_23))
      | ~ v12_waybel_0('#skF_1'(A_23,B_31,C_35),A_23)
      | ~ v1_waybel_0('#skF_1'(A_23,B_31,C_35),A_23)
      | v1_xboole_0('#skF_1'(A_23,B_31,C_35))
      | ~ v2_lattice3(A_23)
      | ~ v1_lattice3(A_23)
      | ~ v2_waybel_1(A_23)
      | r1_waybel_3(A_23,B_31,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_23))
      | ~ m1_subset_1(B_31,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v24_waybel_0(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_24,c_236])).

tff(c_270,plain,(
    ! [B_158,A_159,C_160] :
      ( r1_tarski(B_158,'#skF_2'(A_159,B_158,C_160))
      | r2_hidden(C_160,B_158)
      | ~ m1_subset_1(C_160,u1_struct_0(A_159))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ v12_waybel_0(B_158,A_159)
      | ~ v1_waybel_0(B_158,A_159)
      | v1_xboole_0(B_158)
      | ~ l1_orders_2(A_159)
      | ~ v2_lattice3(A_159)
      | ~ v1_lattice3(A_159)
      | ~ v2_waybel_1(A_159)
      | ~ v5_orders_2(A_159)
      | ~ v4_orders_2(A_159)
      | ~ v3_orders_2(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_434,plain,(
    ! [A_279,B_280,C_281,C_282] :
      ( r1_tarski('#skF_1'(A_279,B_280,C_281),'#skF_2'(A_279,'#skF_1'(A_279,B_280,C_281),C_282))
      | r2_hidden(C_282,'#skF_1'(A_279,B_280,C_281))
      | ~ m1_subset_1(C_282,u1_struct_0(A_279))
      | ~ v12_waybel_0('#skF_1'(A_279,B_280,C_281),A_279)
      | ~ v1_waybel_0('#skF_1'(A_279,B_280,C_281),A_279)
      | v1_xboole_0('#skF_1'(A_279,B_280,C_281))
      | ~ v2_lattice3(A_279)
      | ~ v1_lattice3(A_279)
      | ~ v2_waybel_1(A_279)
      | r1_waybel_3(A_279,B_280,C_281)
      | ~ m1_subset_1(C_281,u1_struct_0(A_279))
      | ~ m1_subset_1(B_280,u1_struct_0(A_279))
      | ~ l1_orders_2(A_279)
      | ~ v24_waybel_0(A_279)
      | ~ v5_orders_2(A_279)
      | ~ v4_orders_2(A_279)
      | ~ v3_orders_2(A_279)
      | v2_struct_0(A_279) ) ),
    inference(resolution,[status(thm)],[c_24,c_270])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k1_yellow_0(A_3,B_4),u1_struct_0(A_3))
      | ~ l1_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_231,plain,(
    ! [A_134,C_135,B_136] :
      ( r3_orders_2(A_134,C_135,k1_yellow_0(A_134,'#skF_1'(A_134,B_136,C_135)))
      | r1_waybel_3(A_134,B_136,C_135)
      | ~ m1_subset_1(C_135,u1_struct_0(A_134))
      | ~ m1_subset_1(B_136,u1_struct_0(A_134))
      | ~ l1_orders_2(A_134)
      | ~ v24_waybel_0(A_134)
      | ~ v5_orders_2(A_134)
      | ~ v4_orders_2(A_134)
      | ~ v3_orders_2(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_16,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_orders_2(A_5,B_6,C_7)
      | ~ r3_orders_2(A_5,B_6,C_7)
      | ~ m1_subset_1(C_7,u1_struct_0(A_5))
      | ~ m1_subset_1(B_6,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5)
      | ~ v3_orders_2(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_304,plain,(
    ! [A_168,C_169,B_170] :
      ( r1_orders_2(A_168,C_169,k1_yellow_0(A_168,'#skF_1'(A_168,B_170,C_169)))
      | ~ m1_subset_1(k1_yellow_0(A_168,'#skF_1'(A_168,B_170,C_169)),u1_struct_0(A_168))
      | r1_waybel_3(A_168,B_170,C_169)
      | ~ m1_subset_1(C_169,u1_struct_0(A_168))
      | ~ m1_subset_1(B_170,u1_struct_0(A_168))
      | ~ l1_orders_2(A_168)
      | ~ v24_waybel_0(A_168)
      | ~ v5_orders_2(A_168)
      | ~ v4_orders_2(A_168)
      | ~ v3_orders_2(A_168)
      | v2_struct_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_231,c_16])).

tff(c_308,plain,(
    ! [A_3,C_169,B_170] :
      ( r1_orders_2(A_3,C_169,k1_yellow_0(A_3,'#skF_1'(A_3,B_170,C_169)))
      | r1_waybel_3(A_3,B_170,C_169)
      | ~ m1_subset_1(C_169,u1_struct_0(A_3))
      | ~ m1_subset_1(B_170,u1_struct_0(A_3))
      | ~ v24_waybel_0(A_3)
      | ~ v5_orders_2(A_3)
      | ~ v4_orders_2(A_3)
      | ~ v3_orders_2(A_3)
      | v2_struct_0(A_3)
      | ~ l1_orders_2(A_3) ) ),
    inference(resolution,[status(thm)],[c_12,c_304])).

tff(c_205,plain,(
    ! [A_111,B_112,C_113] :
      ( r3_orders_2(A_111,k1_yellow_0(A_111,B_112),k1_yellow_0(A_111,C_113))
      | ~ r1_tarski(B_112,C_113)
      | ~ l1_orders_2(A_111)
      | ~ v3_lattice3(A_111)
      | ~ v2_lattice3(A_111)
      | ~ v1_lattice3(A_111)
      | ~ v5_orders_2(A_111)
      | ~ v4_orders_2(A_111)
      | ~ v3_orders_2(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_240,plain,(
    ! [A_143,B_144,C_145] :
      ( r1_orders_2(A_143,k1_yellow_0(A_143,B_144),k1_yellow_0(A_143,C_145))
      | ~ m1_subset_1(k1_yellow_0(A_143,C_145),u1_struct_0(A_143))
      | ~ m1_subset_1(k1_yellow_0(A_143,B_144),u1_struct_0(A_143))
      | v2_struct_0(A_143)
      | ~ r1_tarski(B_144,C_145)
      | ~ l1_orders_2(A_143)
      | ~ v3_lattice3(A_143)
      | ~ v2_lattice3(A_143)
      | ~ v1_lattice3(A_143)
      | ~ v5_orders_2(A_143)
      | ~ v4_orders_2(A_143)
      | ~ v3_orders_2(A_143) ) ),
    inference(resolution,[status(thm)],[c_205,c_16])).

tff(c_32,plain,(
    ! [A_37,B_45,D_51,C_49] :
      ( r1_orders_2(A_37,B_45,D_51)
      | ~ r1_orders_2(A_37,C_49,D_51)
      | ~ r1_orders_2(A_37,B_45,C_49)
      | ~ m1_subset_1(D_51,u1_struct_0(A_37))
      | ~ m1_subset_1(C_49,u1_struct_0(A_37))
      | ~ m1_subset_1(B_45,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37)
      | ~ v4_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_333,plain,(
    ! [A_188,B_189,C_190,B_191] :
      ( r1_orders_2(A_188,B_189,k1_yellow_0(A_188,C_190))
      | ~ r1_orders_2(A_188,B_189,k1_yellow_0(A_188,B_191))
      | ~ m1_subset_1(B_189,u1_struct_0(A_188))
      | ~ m1_subset_1(k1_yellow_0(A_188,C_190),u1_struct_0(A_188))
      | ~ m1_subset_1(k1_yellow_0(A_188,B_191),u1_struct_0(A_188))
      | v2_struct_0(A_188)
      | ~ r1_tarski(B_191,C_190)
      | ~ l1_orders_2(A_188)
      | ~ v3_lattice3(A_188)
      | ~ v2_lattice3(A_188)
      | ~ v1_lattice3(A_188)
      | ~ v5_orders_2(A_188)
      | ~ v4_orders_2(A_188)
      | ~ v3_orders_2(A_188) ) ),
    inference(resolution,[status(thm)],[c_240,c_32])).

tff(c_378,plain,(
    ! [A_212,C_213,C_214,B_215] :
      ( r1_orders_2(A_212,C_213,k1_yellow_0(A_212,C_214))
      | ~ m1_subset_1(k1_yellow_0(A_212,C_214),u1_struct_0(A_212))
      | ~ m1_subset_1(k1_yellow_0(A_212,'#skF_1'(A_212,B_215,C_213)),u1_struct_0(A_212))
      | ~ r1_tarski('#skF_1'(A_212,B_215,C_213),C_214)
      | ~ v3_lattice3(A_212)
      | ~ v2_lattice3(A_212)
      | ~ v1_lattice3(A_212)
      | r1_waybel_3(A_212,B_215,C_213)
      | ~ m1_subset_1(C_213,u1_struct_0(A_212))
      | ~ m1_subset_1(B_215,u1_struct_0(A_212))
      | ~ v24_waybel_0(A_212)
      | ~ v5_orders_2(A_212)
      | ~ v4_orders_2(A_212)
      | ~ v3_orders_2(A_212)
      | v2_struct_0(A_212)
      | ~ l1_orders_2(A_212) ) ),
    inference(resolution,[status(thm)],[c_308,c_333])).

tff(c_383,plain,(
    ! [A_218,C_219,B_220,B_221] :
      ( r1_orders_2(A_218,C_219,k1_yellow_0(A_218,B_220))
      | ~ m1_subset_1(k1_yellow_0(A_218,'#skF_1'(A_218,B_221,C_219)),u1_struct_0(A_218))
      | ~ r1_tarski('#skF_1'(A_218,B_221,C_219),B_220)
      | ~ v3_lattice3(A_218)
      | ~ v2_lattice3(A_218)
      | ~ v1_lattice3(A_218)
      | r1_waybel_3(A_218,B_221,C_219)
      | ~ m1_subset_1(C_219,u1_struct_0(A_218))
      | ~ m1_subset_1(B_221,u1_struct_0(A_218))
      | ~ v24_waybel_0(A_218)
      | ~ v5_orders_2(A_218)
      | ~ v4_orders_2(A_218)
      | ~ v3_orders_2(A_218)
      | v2_struct_0(A_218)
      | ~ l1_orders_2(A_218) ) ),
    inference(resolution,[status(thm)],[c_12,c_378])).

tff(c_387,plain,(
    ! [A_3,C_219,B_220,B_221] :
      ( r1_orders_2(A_3,C_219,k1_yellow_0(A_3,B_220))
      | ~ r1_tarski('#skF_1'(A_3,B_221,C_219),B_220)
      | ~ v3_lattice3(A_3)
      | ~ v2_lattice3(A_3)
      | ~ v1_lattice3(A_3)
      | r1_waybel_3(A_3,B_221,C_219)
      | ~ m1_subset_1(C_219,u1_struct_0(A_3))
      | ~ m1_subset_1(B_221,u1_struct_0(A_3))
      | ~ v24_waybel_0(A_3)
      | ~ v5_orders_2(A_3)
      | ~ v4_orders_2(A_3)
      | ~ v3_orders_2(A_3)
      | v2_struct_0(A_3)
      | ~ l1_orders_2(A_3) ) ),
    inference(resolution,[status(thm)],[c_12,c_383])).

tff(c_475,plain,(
    ! [A_309,C_310,B_311,C_312] :
      ( r1_orders_2(A_309,C_310,k1_yellow_0(A_309,'#skF_2'(A_309,'#skF_1'(A_309,B_311,C_310),C_312)))
      | ~ v3_lattice3(A_309)
      | r2_hidden(C_312,'#skF_1'(A_309,B_311,C_310))
      | ~ m1_subset_1(C_312,u1_struct_0(A_309))
      | ~ v12_waybel_0('#skF_1'(A_309,B_311,C_310),A_309)
      | ~ v1_waybel_0('#skF_1'(A_309,B_311,C_310),A_309)
      | v1_xboole_0('#skF_1'(A_309,B_311,C_310))
      | ~ v2_lattice3(A_309)
      | ~ v1_lattice3(A_309)
      | ~ v2_waybel_1(A_309)
      | r1_waybel_3(A_309,B_311,C_310)
      | ~ m1_subset_1(C_310,u1_struct_0(A_309))
      | ~ m1_subset_1(B_311,u1_struct_0(A_309))
      | ~ l1_orders_2(A_309)
      | ~ v24_waybel_0(A_309)
      | ~ v5_orders_2(A_309)
      | ~ v4_orders_2(A_309)
      | ~ v3_orders_2(A_309)
      | v2_struct_0(A_309) ) ),
    inference(resolution,[status(thm)],[c_434,c_387])).

tff(c_131,plain,(
    ! [A_95,B_96,C_97] :
      ( r3_orders_2(A_95,B_96,C_97)
      | ~ r1_orders_2(A_95,B_96,C_97)
      | ~ m1_subset_1(C_97,u1_struct_0(A_95))
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95)
      | ~ v3_orders_2(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_138,plain,(
    ! [A_3,B_96,B_4] :
      ( r3_orders_2(A_3,B_96,k1_yellow_0(A_3,B_4))
      | ~ r1_orders_2(A_3,B_96,k1_yellow_0(A_3,B_4))
      | ~ m1_subset_1(B_96,u1_struct_0(A_3))
      | ~ v3_orders_2(A_3)
      | v2_struct_0(A_3)
      | ~ l1_orders_2(A_3) ) ),
    inference(resolution,[status(thm)],[c_12,c_131])).

tff(c_274,plain,(
    ! [A_161,B_162,C_163] :
      ( m1_subset_1('#skF_2'(A_161,B_162,C_163),k1_zfmisc_1(u1_struct_0(A_161)))
      | r2_hidden(C_163,B_162)
      | ~ m1_subset_1(C_163,u1_struct_0(A_161))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ v12_waybel_0(B_162,A_161)
      | ~ v1_waybel_0(B_162,A_161)
      | v1_xboole_0(B_162)
      | ~ l1_orders_2(A_161)
      | ~ v2_lattice3(A_161)
      | ~ v1_lattice3(A_161)
      | ~ v2_waybel_1(A_161)
      | ~ v5_orders_2(A_161)
      | ~ v4_orders_2(A_161)
      | ~ v3_orders_2(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_102,plain,(
    ! [D_89] :
      ( r1_waybel_3('#skF_3','#skF_4','#skF_5')
      | r2_hidden('#skF_4',D_89)
      | ~ r3_orders_2('#skF_3','#skF_5',k1_yellow_0('#skF_3',D_89))
      | ~ m1_subset_1(D_89,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_waybel_7(D_89,'#skF_3')
      | ~ v12_waybel_0(D_89,'#skF_3')
      | ~ v1_waybel_0(D_89,'#skF_3')
      | v1_xboole_0(D_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_217,plain,(
    ! [D_89] :
      ( r2_hidden('#skF_4',D_89)
      | ~ r3_orders_2('#skF_3','#skF_5',k1_yellow_0('#skF_3',D_89))
      | ~ m1_subset_1(D_89,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_waybel_7(D_89,'#skF_3')
      | ~ v12_waybel_0(D_89,'#skF_3')
      | ~ v1_waybel_0(D_89,'#skF_3')
      | v1_xboole_0(D_89) ) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_102])).

tff(c_286,plain,(
    ! [B_162,C_163] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3',B_162,C_163))
      | ~ r3_orders_2('#skF_3','#skF_5',k1_yellow_0('#skF_3','#skF_2'('#skF_3',B_162,C_163)))
      | ~ v1_waybel_7('#skF_2'('#skF_3',B_162,C_163),'#skF_3')
      | ~ v12_waybel_0('#skF_2'('#skF_3',B_162,C_163),'#skF_3')
      | ~ v1_waybel_0('#skF_2'('#skF_3',B_162,C_163),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3',B_162,C_163))
      | r2_hidden(C_163,B_162)
      | ~ m1_subset_1(C_163,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v12_waybel_0(B_162,'#skF_3')
      | ~ v1_waybel_0(B_162,'#skF_3')
      | v1_xboole_0(B_162)
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v2_waybel_1('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_274,c_217])).

tff(c_324,plain,(
    ! [B_182,C_183] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3',B_182,C_183))
      | ~ r3_orders_2('#skF_3','#skF_5',k1_yellow_0('#skF_3','#skF_2'('#skF_3',B_182,C_183)))
      | ~ v1_waybel_7('#skF_2'('#skF_3',B_182,C_183),'#skF_3')
      | ~ v12_waybel_0('#skF_2'('#skF_3',B_182,C_183),'#skF_3')
      | ~ v1_waybel_0('#skF_2'('#skF_3',B_182,C_183),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3',B_182,C_183))
      | r2_hidden(C_183,B_182)
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v12_waybel_0(B_182,'#skF_3')
      | ~ v1_waybel_0(B_182,'#skF_3')
      | v1_xboole_0(B_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_56,c_286])).

tff(c_327,plain,(
    ! [B_182,C_183] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3',B_182,C_183))
      | ~ v1_waybel_7('#skF_2'('#skF_3',B_182,C_183),'#skF_3')
      | ~ v12_waybel_0('#skF_2'('#skF_3',B_182,C_183),'#skF_3')
      | ~ v1_waybel_0('#skF_2'('#skF_3',B_182,C_183),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3',B_182,C_183))
      | r2_hidden(C_183,B_182)
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v12_waybel_0(B_182,'#skF_3')
      | ~ v1_waybel_0(B_182,'#skF_3')
      | v1_xboole_0(B_182)
      | ~ r1_orders_2('#skF_3','#skF_5',k1_yellow_0('#skF_3','#skF_2'('#skF_3',B_182,C_183)))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_138,c_324])).

tff(c_330,plain,(
    ! [B_182,C_183] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3',B_182,C_183))
      | ~ v1_waybel_7('#skF_2'('#skF_3',B_182,C_183),'#skF_3')
      | ~ v12_waybel_0('#skF_2'('#skF_3',B_182,C_183),'#skF_3')
      | ~ v1_waybel_0('#skF_2'('#skF_3',B_182,C_183),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3',B_182,C_183))
      | r2_hidden(C_183,B_182)
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v12_waybel_0(B_182,'#skF_3')
      | ~ v1_waybel_0(B_182,'#skF_3')
      | v1_xboole_0(B_182)
      | ~ r1_orders_2('#skF_3','#skF_5',k1_yellow_0('#skF_3','#skF_2'('#skF_3',B_182,C_183)))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_70,c_52,c_327])).

tff(c_331,plain,(
    ! [B_182,C_183] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3',B_182,C_183))
      | ~ v1_waybel_7('#skF_2'('#skF_3',B_182,C_183),'#skF_3')
      | ~ v12_waybel_0('#skF_2'('#skF_3',B_182,C_183),'#skF_3')
      | ~ v1_waybel_0('#skF_2'('#skF_3',B_182,C_183),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3',B_182,C_183))
      | r2_hidden(C_183,B_182)
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v12_waybel_0(B_182,'#skF_3')
      | ~ v1_waybel_0(B_182,'#skF_3')
      | v1_xboole_0(B_182)
      | ~ r1_orders_2('#skF_3','#skF_5',k1_yellow_0('#skF_3','#skF_2'('#skF_3',B_182,C_183))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_330])).

tff(c_487,plain,(
    ! [B_311,C_312] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',B_311,'#skF_5'),C_312))
      | ~ v1_waybel_7('#skF_2'('#skF_3','#skF_1'('#skF_3',B_311,'#skF_5'),C_312),'#skF_3')
      | ~ v12_waybel_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_311,'#skF_5'),C_312),'#skF_3')
      | ~ v1_waybel_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_311,'#skF_5'),C_312),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_311,'#skF_5'),C_312))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_311,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_lattice3('#skF_3')
      | r2_hidden(C_312,'#skF_1'('#skF_3',B_311,'#skF_5'))
      | ~ m1_subset_1(C_312,u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_311,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_311,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_311,'#skF_5'))
      | ~ v2_lattice3('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v2_waybel_1('#skF_3')
      | r1_waybel_3('#skF_3',B_311,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_311,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v24_waybel_0('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_475,c_331])).

tff(c_497,plain,(
    ! [B_311,C_312] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',B_311,'#skF_5'),C_312))
      | ~ v1_waybel_7('#skF_2'('#skF_3','#skF_1'('#skF_3',B_311,'#skF_5'),C_312),'#skF_3')
      | ~ v12_waybel_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_311,'#skF_5'),C_312),'#skF_3')
      | ~ v1_waybel_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_311,'#skF_5'),C_312),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_311,'#skF_5'),C_312))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_311,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r2_hidden(C_312,'#skF_1'('#skF_3',B_311,'#skF_5'))
      | ~ m1_subset_1(C_312,u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_311,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_311,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_311,'#skF_5'))
      | r1_waybel_3('#skF_3',B_311,'#skF_5')
      | ~ m1_subset_1(B_311,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_121,c_56,c_52,c_64,c_62,c_60,c_58,c_487])).

tff(c_541,plain,(
    ! [B_348,C_349] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',B_348,'#skF_5'),C_349))
      | ~ v1_waybel_7('#skF_2'('#skF_3','#skF_1'('#skF_3',B_348,'#skF_5'),C_349),'#skF_3')
      | ~ v12_waybel_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_348,'#skF_5'),C_349),'#skF_3')
      | ~ v1_waybel_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_348,'#skF_5'),C_349),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_348,'#skF_5'),C_349))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_348,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r2_hidden(C_349,'#skF_1'('#skF_3',B_348,'#skF_5'))
      | ~ m1_subset_1(C_349,u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_348,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_348,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_348,'#skF_5'))
      | r1_waybel_3('#skF_3',B_348,'#skF_5')
      | ~ m1_subset_1(B_348,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_497])).

tff(c_544,plain,(
    ! [B_31,C_142] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_142))
      | ~ v12_waybel_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_142),'#skF_3')
      | ~ v1_waybel_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_142),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_142))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_31,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r2_hidden(C_142,'#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ m1_subset_1(C_142,u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ v2_lattice3('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v2_waybel_1('#skF_3')
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v24_waybel_0('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_239,c_541])).

tff(c_547,plain,(
    ! [B_31,C_142] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_142))
      | ~ v12_waybel_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_142),'#skF_3')
      | ~ v1_waybel_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_142),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_142))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_31,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r2_hidden(C_142,'#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ m1_subset_1(C_142,u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_121,c_56,c_52,c_64,c_62,c_60,c_544])).

tff(c_557,plain,(
    ! [B_360,C_361] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',B_360,'#skF_5'),C_361))
      | ~ v12_waybel_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_360,'#skF_5'),C_361),'#skF_3')
      | ~ v1_waybel_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_360,'#skF_5'),C_361),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_360,'#skF_5'),C_361))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_360,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r2_hidden(C_361,'#skF_1'('#skF_3',B_360,'#skF_5'))
      | ~ m1_subset_1(C_361,u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_360,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_360,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_360,'#skF_5'))
      | r1_waybel_3('#skF_3',B_360,'#skF_5')
      | ~ m1_subset_1(B_360,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_547])).

tff(c_560,plain,(
    ! [B_31,C_157] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_157))
      | ~ v12_waybel_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_157),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_157))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_31,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r2_hidden(C_157,'#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ m1_subset_1(C_157,u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ v2_lattice3('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v2_waybel_1('#skF_3')
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v24_waybel_0('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_269,c_557])).

tff(c_563,plain,(
    ! [B_31,C_157] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_157))
      | ~ v12_waybel_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_157),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_157))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_31,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r2_hidden(C_157,'#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ m1_subset_1(C_157,u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_121,c_56,c_52,c_64,c_62,c_60,c_560])).

tff(c_565,plain,(
    ! [B_362,C_363] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',B_362,'#skF_5'),C_363))
      | ~ v12_waybel_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_362,'#skF_5'),C_363),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_362,'#skF_5'),C_363))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_362,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r2_hidden(C_363,'#skF_1'('#skF_3',B_362,'#skF_5'))
      | ~ m1_subset_1(C_363,u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_362,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_362,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_362,'#skF_5'))
      | r1_waybel_3('#skF_3',B_362,'#skF_5')
      | ~ m1_subset_1(B_362,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_563])).

tff(c_568,plain,(
    ! [B_31,C_151] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_151))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_151))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_31,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r2_hidden(C_151,'#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ m1_subset_1(C_151,u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ v2_lattice3('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v2_waybel_1('#skF_3')
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v24_waybel_0('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_248,c_565])).

tff(c_571,plain,(
    ! [B_31,C_151] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_151))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_151))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_31,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r2_hidden(C_151,'#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ m1_subset_1(C_151,u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_121,c_56,c_52,c_64,c_62,c_60,c_568])).

tff(c_573,plain,(
    ! [B_364,C_365] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',B_364,'#skF_5'),C_365))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_364,'#skF_5'),C_365))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_364,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r2_hidden(C_365,'#skF_1'('#skF_3',B_364,'#skF_5'))
      | ~ m1_subset_1(C_365,u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_364,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_364,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_364,'#skF_5'))
      | r1_waybel_3('#skF_3',B_364,'#skF_5')
      | ~ m1_subset_1(B_364,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_571])).

tff(c_576,plain,(
    ! [B_31,C_365] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_365))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_365))
      | r2_hidden(C_365,'#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ m1_subset_1(C_365,u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v24_waybel_0('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_573])).

tff(c_579,plain,(
    ! [B_31,C_365] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_365))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),C_365))
      | r2_hidden(C_365,'#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ m1_subset_1(C_365,u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_121,c_56,c_52,c_576])).

tff(c_588,plain,(
    ! [B_371,C_372] :
      ( r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_1'('#skF_3',B_371,'#skF_5'),C_372))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_371,'#skF_5'),C_372))
      | r2_hidden(C_372,'#skF_1'('#skF_3',B_371,'#skF_5'))
      | ~ m1_subset_1(C_372,u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_371,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_371,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_371,'#skF_5'))
      | r1_waybel_3('#skF_3',B_371,'#skF_5')
      | ~ m1_subset_1(B_371,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_579])).

tff(c_34,plain,(
    ! [C_64,A_52,B_60] :
      ( ~ r2_hidden(C_64,'#skF_2'(A_52,B_60,C_64))
      | r2_hidden(C_64,B_60)
      | ~ m1_subset_1(C_64,u1_struct_0(A_52))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ v12_waybel_0(B_60,A_52)
      | ~ v1_waybel_0(B_60,A_52)
      | v1_xboole_0(B_60)
      | ~ l1_orders_2(A_52)
      | ~ v2_lattice3(A_52)
      | ~ v1_lattice3(A_52)
      | ~ v2_waybel_1(A_52)
      | ~ v5_orders_2(A_52)
      | ~ v4_orders_2(A_52)
      | ~ v3_orders_2(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_591,plain,(
    ! [B_371] :
      ( ~ m1_subset_1('#skF_1'('#skF_3',B_371,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v2_waybel_1('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_371,'#skF_5'),'#skF_4'))
      | r2_hidden('#skF_4','#skF_1'('#skF_3',B_371,'#skF_5'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_371,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_371,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_371,'#skF_5'))
      | r1_waybel_3('#skF_3',B_371,'#skF_5')
      | ~ m1_subset_1(B_371,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_588,c_34])).

tff(c_595,plain,(
    ! [B_373] :
      ( ~ m1_subset_1('#skF_1'('#skF_3',B_373,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_373,'#skF_5'),'#skF_4'))
      | r2_hidden('#skF_4','#skF_1'('#skF_3',B_373,'#skF_5'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_373,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_373,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_373,'#skF_5'))
      | r1_waybel_3('#skF_3',B_373,'#skF_5')
      | ~ m1_subset_1(B_373,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_70,c_68,c_66,c_64,c_62,c_60,c_56,c_591])).

tff(c_599,plain,(
    ! [B_31] :
      ( v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_4'))
      | r2_hidden('#skF_4','#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v24_waybel_0('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_595])).

tff(c_602,plain,(
    ! [B_31] :
      ( v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_4'))
      | r2_hidden('#skF_4','#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_121,c_56,c_52,c_599])).

tff(c_604,plain,(
    ! [B_374] :
      ( v1_xboole_0('#skF_2'('#skF_3','#skF_1'('#skF_3',B_374,'#skF_5'),'#skF_4'))
      | r2_hidden('#skF_4','#skF_1'('#skF_3',B_374,'#skF_5'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_374,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_374,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_374,'#skF_5'))
      | r1_waybel_3('#skF_3',B_374,'#skF_5')
      | ~ m1_subset_1(B_374,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_602])).

tff(c_46,plain,(
    ! [A_52,B_60,C_64] :
      ( ~ v1_xboole_0('#skF_2'(A_52,B_60,C_64))
      | r2_hidden(C_64,B_60)
      | ~ m1_subset_1(C_64,u1_struct_0(A_52))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ v12_waybel_0(B_60,A_52)
      | ~ v1_waybel_0(B_60,A_52)
      | v1_xboole_0(B_60)
      | ~ l1_orders_2(A_52)
      | ~ v2_lattice3(A_52)
      | ~ v1_lattice3(A_52)
      | ~ v2_waybel_1(A_52)
      | ~ v5_orders_2(A_52)
      | ~ v4_orders_2(A_52)
      | ~ v3_orders_2(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_606,plain,(
    ! [B_374] :
      ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_374,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v2_lattice3('#skF_3')
      | ~ v1_lattice3('#skF_3')
      | ~ v2_waybel_1('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | r2_hidden('#skF_4','#skF_1'('#skF_3',B_374,'#skF_5'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_374,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_374,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_374,'#skF_5'))
      | r1_waybel_3('#skF_3',B_374,'#skF_5')
      | ~ m1_subset_1(B_374,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_604,c_46])).

tff(c_610,plain,(
    ! [B_375] :
      ( ~ m1_subset_1('#skF_1'('#skF_3',B_375,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r2_hidden('#skF_4','#skF_1'('#skF_3',B_375,'#skF_5'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_375,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_375,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_375,'#skF_5'))
      | r1_waybel_3('#skF_3',B_375,'#skF_5')
      | ~ m1_subset_1(B_375,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_56,c_54,c_606])).

tff(c_614,plain,(
    ! [B_31] :
      ( r2_hidden('#skF_4','#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v24_waybel_0('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_610])).

tff(c_617,plain,(
    ! [B_31] :
      ( r2_hidden('#skF_4','#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_121,c_56,c_52,c_614])).

tff(c_619,plain,(
    ! [B_376] :
      ( r2_hidden('#skF_4','#skF_1'('#skF_3',B_376,'#skF_5'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_376,'#skF_5'),'#skF_3')
      | ~ v1_waybel_0('#skF_1'('#skF_3',B_376,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_376,'#skF_5'))
      | r1_waybel_3('#skF_3',B_376,'#skF_5')
      | ~ m1_subset_1(B_376,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_617])).

tff(c_623,plain,(
    ! [B_31] :
      ( r2_hidden('#skF_4','#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v24_waybel_0('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_619])).

tff(c_626,plain,(
    ! [B_31] :
      ( r2_hidden('#skF_4','#skF_1'('#skF_3',B_31,'#skF_5'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_31,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_121,c_56,c_52,c_623])).

tff(c_628,plain,(
    ! [B_377] :
      ( r2_hidden('#skF_4','#skF_1'('#skF_3',B_377,'#skF_5'))
      | ~ v12_waybel_0('#skF_1'('#skF_3',B_377,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_1'('#skF_3',B_377,'#skF_5'))
      | r1_waybel_3('#skF_3',B_377,'#skF_5')
      | ~ m1_subset_1(B_377,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_626])).

tff(c_632,plain,(
    ! [B_31] :
      ( r2_hidden('#skF_4','#skF_1'('#skF_3',B_31,'#skF_5'))
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v24_waybel_0('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_628])).

tff(c_635,plain,(
    ! [B_31] :
      ( r2_hidden('#skF_4','#skF_1'('#skF_3',B_31,'#skF_5'))
      | v1_xboole_0('#skF_1'('#skF_3',B_31,'#skF_5'))
      | r1_waybel_3('#skF_3',B_31,'#skF_5')
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_121,c_56,c_52,c_632])).

tff(c_637,plain,(
    ! [B_378] :
      ( r2_hidden('#skF_4','#skF_1'('#skF_3',B_378,'#skF_5'))
      | v1_xboole_0('#skF_1'('#skF_3',B_378,'#skF_5'))
      | r1_waybel_3('#skF_3',B_378,'#skF_5')
      | ~ m1_subset_1(B_378,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_635])).

tff(c_20,plain,(
    ! [B_31,A_23,C_35] :
      ( ~ r2_hidden(B_31,'#skF_1'(A_23,B_31,C_35))
      | r1_waybel_3(A_23,B_31,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_23))
      | ~ m1_subset_1(B_31,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v24_waybel_0(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_641,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v24_waybel_0('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r1_waybel_3('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_637,c_20])).

tff(c_644,plain,
    ( v2_struct_0('#skF_3')
    | v1_xboole_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r1_waybel_3('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_70,c_68,c_66,c_121,c_56,c_52,c_641])).

tff(c_645,plain,(
    v1_xboole_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_122,c_644])).

tff(c_30,plain,(
    ! [A_23,B_31,C_35] :
      ( ~ v1_xboole_0('#skF_1'(A_23,B_31,C_35))
      | r1_waybel_3(A_23,B_31,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_23))
      | ~ m1_subset_1(B_31,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v24_waybel_0(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_647,plain,
    ( r1_waybel_3('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v24_waybel_0('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_645,c_30])).

tff(c_650,plain,
    ( r1_waybel_3('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_121,c_56,c_54,c_52,c_647])).

tff(c_652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_104,c_650])).

tff(c_654,plain,(
    r1_waybel_3('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_72,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r1_waybel_3('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_656,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_72])).

tff(c_666,plain,(
    ! [A_381] :
      ( v24_waybel_0(A_381)
      | ~ v3_lattice3(A_381)
      | ~ v3_orders_2(A_381)
      | v2_struct_0(A_381)
      | ~ l1_orders_2(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_669,plain,
    ( v24_waybel_0('#skF_3')
    | ~ v3_lattice3('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_666])).

tff(c_672,plain,
    ( v24_waybel_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_669])).

tff(c_673,plain,(
    v2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_672])).

tff(c_676,plain,
    ( ~ v2_lattice3('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_673,c_10])).

tff(c_680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_676])).

tff(c_682,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_672])).

tff(c_653,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_82,plain,
    ( v1_waybel_0('#skF_6','#skF_3')
    | ~ r1_waybel_3('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_658,plain,(
    v1_waybel_0('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_82])).

tff(c_80,plain,
    ( v12_waybel_0('#skF_6','#skF_3')
    | ~ r1_waybel_3('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_662,plain,(
    v12_waybel_0('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_80])).

tff(c_76,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ r1_waybel_3('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_665,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_76])).

tff(c_74,plain,
    ( r3_orders_2('#skF_3','#skF_5',k1_yellow_0('#skF_3','#skF_6'))
    | ~ r1_waybel_3('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_692,plain,(
    r3_orders_2('#skF_3','#skF_5',k1_yellow_0('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_74])).

tff(c_936,plain,(
    ! [B_462,D_463,A_464,C_465] :
      ( r2_hidden(B_462,D_463)
      | ~ r3_orders_2(A_464,C_465,k1_yellow_0(A_464,D_463))
      | ~ m1_subset_1(D_463,k1_zfmisc_1(u1_struct_0(A_464)))
      | ~ v12_waybel_0(D_463,A_464)
      | ~ v1_waybel_0(D_463,A_464)
      | v1_xboole_0(D_463)
      | ~ r1_waybel_3(A_464,B_462,C_465)
      | ~ m1_subset_1(C_465,u1_struct_0(A_464))
      | ~ m1_subset_1(B_462,u1_struct_0(A_464))
      | ~ l1_orders_2(A_464)
      | ~ v4_orders_2(A_464)
      | ~ v3_orders_2(A_464)
      | v2_struct_0(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_946,plain,(
    ! [B_462] :
      ( r2_hidden(B_462,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v12_waybel_0('#skF_6','#skF_3')
      | ~ v1_waybel_0('#skF_6','#skF_3')
      | v1_xboole_0('#skF_6')
      | ~ r1_waybel_3('#skF_3',B_462,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_462,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_692,c_936])).

tff(c_956,plain,(
    ! [B_462] :
      ( r2_hidden(B_462,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ r1_waybel_3('#skF_3',B_462,'#skF_5')
      | ~ m1_subset_1(B_462,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_56,c_52,c_658,c_662,c_665,c_946])).

tff(c_958,plain,(
    ! [B_466] :
      ( r2_hidden(B_466,'#skF_6')
      | ~ r1_waybel_3('#skF_3',B_466,'#skF_5')
      | ~ m1_subset_1(B_466,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_682,c_653,c_956])).

tff(c_968,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r1_waybel_3('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_958])).

tff(c_978,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_968])).

tff(c_980,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_656,c_978])).

%------------------------------------------------------------------------------
