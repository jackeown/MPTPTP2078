%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:45 EST 2020

% Result     : Theorem 9.17s
% Output     : CNFRefutation 9.58s
% Verified   : 
% Statistics : Number of formulae       :  301 (7932 expanded)
%              Number of leaves         :   44 (2943 expanded)
%              Depth                    :   34
%              Number of atoms          : 1445 (49930 expanded)
%              Number of equality atoms :  101 (3035 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tmap_1,type,(
    k4_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_357,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
               => ( ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,u1_struct_0(B))
                       => D = k1_funct_1(C,D) ) )
                 => r2_funct_2(u1_struct_0(B),u1_struct_0(A),k4_tmap_1(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).

tff(f_210,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( r2_funct_2(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_221,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_195,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_295,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                 => r2_funct_2(u1_struct_0(C),u1_struct_0(B),D,k3_tmap_1(A,B,C,C,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_165,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_265,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,B) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(A))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(A)))) )
                     => ( ! [F] :
                            ( m1_subset_1(F,u1_struct_0(B))
                           => ( r2_hidden(F,u1_struct_0(C))
                             => k3_funct_2(u1_struct_0(B),u1_struct_0(A),D,F) = k1_funct_1(E,F) ) )
                       => r2_funct_2(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_327,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,u1_struct_0(B))
               => k1_funct_1(k4_tmap_1(A,B),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

tff(f_217,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_357])).

tff(c_70,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_357])).

tff(c_68,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_357])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_357])).

tff(c_32,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1(k4_tmap_1(A_86,B_87),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_87),u1_struct_0(A_86))))
      | ~ m1_pre_topc(B_87,A_86)
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_54,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_357])).

tff(c_36,plain,(
    ! [A_86,B_87] :
      ( v1_funct_1(k4_tmap_1(A_86,B_87))
      | ~ m1_pre_topc(B_87,A_86)
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_357])).

tff(c_60,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_357])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_357])).

tff(c_3670,plain,(
    ! [A_689,B_690,C_691,D_692] :
      ( m1_subset_1('#skF_1'(A_689,B_690,C_691,D_692),A_689)
      | r2_funct_2(A_689,B_690,C_691,D_692)
      | ~ m1_subset_1(D_692,k1_zfmisc_1(k2_zfmisc_1(A_689,B_690)))
      | ~ v1_funct_2(D_692,A_689,B_690)
      | ~ v1_funct_1(D_692)
      | ~ m1_subset_1(C_691,k1_zfmisc_1(k2_zfmisc_1(A_689,B_690)))
      | ~ v1_funct_2(C_691,A_689,B_690)
      | ~ v1_funct_1(C_691) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3674,plain,(
    ! [C_691] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_691,'#skF_5'),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_691,'#skF_5')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_691,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_691,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_691) ) ),
    inference(resolution,[status(thm)],[c_58,c_3670])).

tff(c_3678,plain,(
    ! [C_691] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_691,'#skF_5'),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_691,'#skF_5')
      | ~ m1_subset_1(C_691,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_691,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_691) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_3674])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_357])).

tff(c_3679,plain,(
    ! [C_693] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_693,'#skF_5'),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_693,'#skF_5')
      | ~ m1_subset_1(C_693,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_693,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_693) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_3674])).

tff(c_20,plain,(
    ! [C_34,A_28,B_32] :
      ( m1_subset_1(C_34,u1_struct_0(A_28))
      | ~ m1_subset_1(C_34,u1_struct_0(B_32))
      | ~ m1_pre_topc(B_32,A_28)
      | v2_struct_0(B_32)
      | ~ l1_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3683,plain,(
    ! [C_693,A_28] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_693,'#skF_5'),u1_struct_0(A_28))
      | ~ m1_pre_topc('#skF_4',A_28)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_28)
      | v2_struct_0(A_28)
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_693,'#skF_5')
      | ~ m1_subset_1(C_693,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_693,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_693) ) ),
    inference(resolution,[status(thm)],[c_3679,c_20])).

tff(c_3704,plain,(
    ! [C_699,A_700] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_699,'#skF_5'),u1_struct_0(A_700))
      | ~ m1_pre_topc('#skF_4',A_700)
      | ~ l1_pre_topc(A_700)
      | v2_struct_0(A_700)
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_699,'#skF_5')
      | ~ m1_subset_1(C_699,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_699,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_699) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3683])).

tff(c_74,plain,(
    ! [B_196,A_197] :
      ( l1_pre_topc(B_196)
      | ~ m1_pre_topc(B_196,A_197)
      | ~ l1_pre_topc(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_80,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_74])).

tff(c_84,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_80])).

tff(c_40,plain,(
    ! [A_91] :
      ( m1_pre_topc(A_91,A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_176,plain,(
    ! [A_246,B_247,C_248,D_249] :
      ( m1_subset_1('#skF_1'(A_246,B_247,C_248,D_249),A_246)
      | r2_funct_2(A_246,B_247,C_248,D_249)
      | ~ m1_subset_1(D_249,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247)))
      | ~ v1_funct_2(D_249,A_246,B_247)
      | ~ v1_funct_1(D_249)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247)))
      | ~ v1_funct_2(C_248,A_246,B_247)
      | ~ v1_funct_1(C_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_180,plain,(
    ! [C_248] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_248,'#skF_5'),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_248,'#skF_5')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_248,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_248) ) ),
    inference(resolution,[status(thm)],[c_58,c_176])).

tff(c_185,plain,(
    ! [C_250] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_250,'#skF_5'),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_250,'#skF_5')
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_250,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_180])).

tff(c_192,plain,(
    ! [C_250,A_28] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_250,'#skF_5'),u1_struct_0(A_28))
      | ~ m1_pre_topc('#skF_4',A_28)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_28)
      | v2_struct_0(A_28)
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_250,'#skF_5')
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_250,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_250) ) ),
    inference(resolution,[status(thm)],[c_185,c_20])).

tff(c_215,plain,(
    ! [C_256,A_257] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_256,'#skF_5'),u1_struct_0(A_257))
      | ~ m1_pre_topc('#skF_4',A_257)
      | ~ l1_pre_topc(A_257)
      | v2_struct_0(A_257)
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_256,'#skF_5')
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_256,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_256) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_192])).

tff(c_489,plain,(
    ! [C_326,A_327,A_328] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5'),u1_struct_0(A_327))
      | ~ m1_pre_topc(A_328,A_327)
      | ~ l1_pre_topc(A_327)
      | v2_struct_0(A_327)
      | ~ m1_pre_topc('#skF_4',A_328)
      | ~ l1_pre_topc(A_328)
      | v2_struct_0(A_328)
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5')
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_326,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_326) ) ),
    inference(resolution,[status(thm)],[c_215,c_20])).

tff(c_493,plain,(
    ! [C_326] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5'),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5')
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_326,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_326) ) ),
    inference(resolution,[status(thm)],[c_64,c_489])).

tff(c_497,plain,(
    ! [C_326] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5'),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | v2_struct_0('#skF_4')
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5')
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_326,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_68,c_493])).

tff(c_498,plain,(
    ! [C_326] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5')
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_326,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_326) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_72,c_497])).

tff(c_499,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_498])).

tff(c_515,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_499])).

tff(c_519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_515])).

tff(c_521,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_498])).

tff(c_143,plain,(
    ! [A_224,B_225,D_226] :
      ( r2_funct_2(A_224,B_225,D_226,D_226)
      | ~ m1_subset_1(D_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225)))
      | ~ v1_funct_2(D_226,A_224,B_225)
      | ~ v1_funct_1(D_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_145,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_143])).

tff(c_148,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_145])).

tff(c_90,plain,(
    ! [B_203,A_204] :
      ( v2_pre_topc(B_203)
      | ~ m1_pre_topc(B_203,A_204)
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_96,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_90])).

tff(c_100,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_96])).

tff(c_295,plain,(
    ! [A_274,B_278,E_275,D_277,C_276] :
      ( v1_funct_1(k3_tmap_1(A_274,B_278,C_276,D_277,E_275))
      | ~ m1_subset_1(E_275,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_276),u1_struct_0(B_278))))
      | ~ v1_funct_2(E_275,u1_struct_0(C_276),u1_struct_0(B_278))
      | ~ v1_funct_1(E_275)
      | ~ m1_pre_topc(D_277,A_274)
      | ~ m1_pre_topc(C_276,A_274)
      | ~ l1_pre_topc(B_278)
      | ~ v2_pre_topc(B_278)
      | v2_struct_0(B_278)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_299,plain,(
    ! [A_274,D_277] :
      ( v1_funct_1(k3_tmap_1(A_274,'#skF_3','#skF_4',D_277,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_277,A_274)
      | ~ m1_pre_topc('#skF_4',A_274)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(resolution,[status(thm)],[c_58,c_295])).

tff(c_303,plain,(
    ! [A_274,D_277] :
      ( v1_funct_1(k3_tmap_1(A_274,'#skF_3','#skF_4',D_277,'#skF_5'))
      | ~ m1_pre_topc(D_277,A_274)
      | ~ m1_pre_topc('#skF_4',A_274)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_62,c_60,c_299])).

tff(c_304,plain,(
    ! [A_274,D_277] :
      ( v1_funct_1(k3_tmap_1(A_274,'#skF_3','#skF_4',D_277,'#skF_5'))
      | ~ m1_pre_topc(D_277,A_274)
      | ~ m1_pre_topc('#skF_4',A_274)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_303])).

tff(c_334,plain,(
    ! [D_301,E_299,B_302,C_300,A_298] :
      ( v1_funct_2(k3_tmap_1(A_298,B_302,C_300,D_301,E_299),u1_struct_0(D_301),u1_struct_0(B_302))
      | ~ m1_subset_1(E_299,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_300),u1_struct_0(B_302))))
      | ~ v1_funct_2(E_299,u1_struct_0(C_300),u1_struct_0(B_302))
      | ~ v1_funct_1(E_299)
      | ~ m1_pre_topc(D_301,A_298)
      | ~ m1_pre_topc(C_300,A_298)
      | ~ l1_pre_topc(B_302)
      | ~ v2_pre_topc(B_302)
      | v2_struct_0(B_302)
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298)
      | v2_struct_0(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_338,plain,(
    ! [A_298,D_301] :
      ( v1_funct_2(k3_tmap_1(A_298,'#skF_3','#skF_4',D_301,'#skF_5'),u1_struct_0(D_301),u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_301,A_298)
      | ~ m1_pre_topc('#skF_4',A_298)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298)
      | v2_struct_0(A_298) ) ),
    inference(resolution,[status(thm)],[c_58,c_334])).

tff(c_342,plain,(
    ! [A_298,D_301] :
      ( v1_funct_2(k3_tmap_1(A_298,'#skF_3','#skF_4',D_301,'#skF_5'),u1_struct_0(D_301),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_301,A_298)
      | ~ m1_pre_topc('#skF_4',A_298)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298)
      | v2_struct_0(A_298) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_62,c_60,c_338])).

tff(c_343,plain,(
    ! [A_298,D_301] :
      ( v1_funct_2(k3_tmap_1(A_298,'#skF_3','#skF_4',D_301,'#skF_5'),u1_struct_0(D_301),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_301,A_298)
      | ~ m1_pre_topc('#skF_4',A_298)
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298)
      | v2_struct_0(A_298) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_342])).

tff(c_26,plain,(
    ! [A_81,D_84,B_82,E_85,C_83] :
      ( m1_subset_1(k3_tmap_1(A_81,B_82,C_83,D_84,E_85),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_84),u1_struct_0(B_82))))
      | ~ m1_subset_1(E_85,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_83),u1_struct_0(B_82))))
      | ~ v1_funct_2(E_85,u1_struct_0(C_83),u1_struct_0(B_82))
      | ~ v1_funct_1(E_85)
      | ~ m1_pre_topc(D_84,A_81)
      | ~ m1_pre_topc(C_83,A_81)
      | ~ l1_pre_topc(B_82)
      | ~ v2_pre_topc(B_82)
      | v2_struct_0(B_82)
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_345,plain,(
    ! [C_305,B_306,D_307,A_308] :
      ( r2_funct_2(u1_struct_0(C_305),u1_struct_0(B_306),D_307,k3_tmap_1(A_308,B_306,C_305,C_305,D_307))
      | ~ m1_subset_1(D_307,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_305),u1_struct_0(B_306))))
      | ~ v1_funct_2(D_307,u1_struct_0(C_305),u1_struct_0(B_306))
      | ~ v1_funct_1(D_307)
      | ~ m1_pre_topc(C_305,A_308)
      | v2_struct_0(C_305)
      | ~ l1_pre_topc(B_306)
      | ~ v2_pre_topc(B_306)
      | v2_struct_0(B_306)
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_349,plain,(
    ! [A_308] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_308,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_308)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(resolution,[status(thm)],[c_58,c_345])).

tff(c_353,plain,(
    ! [A_308] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_308,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_308)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_62,c_60,c_349])).

tff(c_355,plain,(
    ! [A_309] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_309,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_309)
      | ~ l1_pre_topc(A_309)
      | ~ v2_pre_topc(A_309)
      | v2_struct_0(A_309) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_353])).

tff(c_14,plain,(
    ! [D_21,C_20,A_18,B_19] :
      ( D_21 = C_20
      | ~ r2_funct_2(A_18,B_19,C_20,D_21)
      | ~ m1_subset_1(D_21,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(D_21,A_18,B_19)
      | ~ v1_funct_1(D_21)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_357,plain,(
    ! [A_309] :
      ( k3_tmap_1(A_309,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_subset_1(k3_tmap_1(A_309,'#skF_3','#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k3_tmap_1(A_309,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_309,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_309)
      | ~ l1_pre_topc(A_309)
      | ~ v2_pre_topc(A_309)
      | v2_struct_0(A_309) ) ),
    inference(resolution,[status(thm)],[c_355,c_14])).

tff(c_396,plain,(
    ! [A_322] :
      ( k3_tmap_1(A_322,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_subset_1(k3_tmap_1(A_322,'#skF_3','#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k3_tmap_1(A_322,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_322,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_322)
      | ~ l1_pre_topc(A_322)
      | ~ v2_pre_topc(A_322)
      | v2_struct_0(A_322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_357])).

tff(c_400,plain,(
    ! [A_81] :
      ( k3_tmap_1(A_81,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_81,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_81,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_81)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_26,c_396])).

tff(c_403,plain,(
    ! [A_81] :
      ( k3_tmap_1(A_81,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_81,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_81,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_81)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_62,c_60,c_58,c_400])).

tff(c_405,plain,(
    ! [A_323] :
      ( k3_tmap_1(A_323,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_323,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_323,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_323)
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323)
      | v2_struct_0(A_323) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_403])).

tff(c_411,plain,(
    ! [A_324] :
      ( k3_tmap_1(A_324,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_1(k3_tmap_1(A_324,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_324)
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(resolution,[status(thm)],[c_343,c_405])).

tff(c_417,plain,(
    ! [A_325] :
      ( k3_tmap_1(A_325,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_pre_topc('#skF_4',A_325)
      | ~ l1_pre_topc(A_325)
      | ~ v2_pre_topc(A_325)
      | v2_struct_0(A_325) ) ),
    inference(resolution,[status(thm)],[c_304,c_411])).

tff(c_421,plain,
    ( k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_417])).

tff(c_427,plain,
    ( k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_100,c_421])).

tff(c_428,plain,(
    k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_427])).

tff(c_1051,plain,(
    ! [E_397,A_396,D_398,B_400,C_399] :
      ( k3_tmap_1(A_396,B_400,C_399,D_398,E_397) = k2_partfun1(u1_struct_0(C_399),u1_struct_0(B_400),E_397,u1_struct_0(D_398))
      | ~ m1_pre_topc(D_398,C_399)
      | ~ m1_subset_1(E_397,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_399),u1_struct_0(B_400))))
      | ~ v1_funct_2(E_397,u1_struct_0(C_399),u1_struct_0(B_400))
      | ~ v1_funct_1(E_397)
      | ~ m1_pre_topc(D_398,A_396)
      | ~ m1_pre_topc(C_399,A_396)
      | ~ l1_pre_topc(B_400)
      | ~ v2_pre_topc(B_400)
      | v2_struct_0(B_400)
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1057,plain,(
    ! [A_396,D_398] :
      ( k3_tmap_1(A_396,'#skF_3','#skF_4',D_398,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_398))
      | ~ m1_pre_topc(D_398,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_398,A_396)
      | ~ m1_pre_topc('#skF_4',A_396)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(resolution,[status(thm)],[c_58,c_1051])).

tff(c_1062,plain,(
    ! [A_396,D_398] :
      ( k3_tmap_1(A_396,'#skF_3','#skF_4',D_398,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_398))
      | ~ m1_pre_topc(D_398,'#skF_4')
      | ~ m1_pre_topc(D_398,A_396)
      | ~ m1_pre_topc('#skF_4',A_396)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_62,c_60,c_1057])).

tff(c_1064,plain,(
    ! [A_401,D_402] :
      ( k3_tmap_1(A_401,'#skF_3','#skF_4',D_402,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_402))
      | ~ m1_pre_topc(D_402,'#skF_4')
      | ~ m1_pre_topc(D_402,A_401)
      | ~ m1_pre_topc('#skF_4',A_401)
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1062])).

tff(c_1068,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_521,c_1064])).

tff(c_1079,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_84,c_521,c_428,c_1068])).

tff(c_1080,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1079])).

tff(c_315,plain,(
    ! [A_293,B_294,C_295,D_296] :
      ( k2_partfun1(u1_struct_0(A_293),u1_struct_0(B_294),C_295,u1_struct_0(D_296)) = k2_tmap_1(A_293,B_294,C_295,D_296)
      | ~ m1_pre_topc(D_296,A_293)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_293),u1_struct_0(B_294))))
      | ~ v1_funct_2(C_295,u1_struct_0(A_293),u1_struct_0(B_294))
      | ~ v1_funct_1(C_295)
      | ~ l1_pre_topc(B_294)
      | ~ v2_pre_topc(B_294)
      | v2_struct_0(B_294)
      | ~ l1_pre_topc(A_293)
      | ~ v2_pre_topc(A_293)
      | v2_struct_0(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_319,plain,(
    ! [D_296] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_296)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_296)
      | ~ m1_pre_topc(D_296,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_315])).

tff(c_323,plain,(
    ! [D_296] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_296)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_296)
      | ~ m1_pre_topc(D_296,'#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_84,c_70,c_68,c_62,c_60,c_319])).

tff(c_324,plain,(
    ! [D_296] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_296)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_296)
      | ~ m1_pre_topc(D_296,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_72,c_323])).

tff(c_1089,plain,
    ( k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_324])).

tff(c_1096,plain,(
    k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_1089])).

tff(c_1397,plain,(
    ! [C_427,B_425,D_424,A_426,E_423] :
      ( r2_hidden('#skF_2'(E_423,D_424,B_425,A_426,C_427),u1_struct_0(C_427))
      | r2_funct_2(u1_struct_0(C_427),u1_struct_0(A_426),k2_tmap_1(B_425,A_426,D_424,C_427),E_423)
      | ~ m1_subset_1(E_423,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_427),u1_struct_0(A_426))))
      | ~ v1_funct_2(E_423,u1_struct_0(C_427),u1_struct_0(A_426))
      | ~ v1_funct_1(E_423)
      | ~ m1_subset_1(D_424,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_425),u1_struct_0(A_426))))
      | ~ v1_funct_2(D_424,u1_struct_0(B_425),u1_struct_0(A_426))
      | ~ v1_funct_1(D_424)
      | ~ m1_pre_topc(C_427,B_425)
      | v2_struct_0(C_427)
      | ~ l1_pre_topc(B_425)
      | ~ v2_pre_topc(B_425)
      | v2_struct_0(B_425)
      | ~ l1_pre_topc(A_426)
      | ~ v2_pre_topc(A_426)
      | v2_struct_0(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_2079,plain,(
    ! [A_512,B_513,D_514,B_515] :
      ( r2_hidden('#skF_2'(k4_tmap_1(A_512,B_513),D_514,B_515,A_512,B_513),u1_struct_0(B_513))
      | r2_funct_2(u1_struct_0(B_513),u1_struct_0(A_512),k2_tmap_1(B_515,A_512,D_514,B_513),k4_tmap_1(A_512,B_513))
      | ~ v1_funct_2(k4_tmap_1(A_512,B_513),u1_struct_0(B_513),u1_struct_0(A_512))
      | ~ v1_funct_1(k4_tmap_1(A_512,B_513))
      | ~ m1_subset_1(D_514,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_515),u1_struct_0(A_512))))
      | ~ v1_funct_2(D_514,u1_struct_0(B_515),u1_struct_0(A_512))
      | ~ v1_funct_1(D_514)
      | ~ m1_pre_topc(B_513,B_515)
      | v2_struct_0(B_513)
      | ~ l1_pre_topc(B_515)
      | ~ v2_pre_topc(B_515)
      | v2_struct_0(B_515)
      | ~ m1_pre_topc(B_513,A_512)
      | ~ l1_pre_topc(A_512)
      | ~ v2_pre_topc(A_512)
      | v2_struct_0(A_512) ) ),
    inference(resolution,[status(thm)],[c_32,c_1397])).

tff(c_2084,plain,
    ( r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4','#skF_3','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1096,c_2079])).

tff(c_2087,plain,
    ( r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4','#skF_3','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_100,c_84,c_521,c_62,c_60,c_58,c_2084])).

tff(c_2088,plain,
    ( r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4','#skF_3','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_2087])).

tff(c_2089,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2088])).

tff(c_2092,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_2089])).

tff(c_2095,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_2092])).

tff(c_2097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2095])).

tff(c_2099,plain,(
    v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2088])).

tff(c_34,plain,(
    ! [A_86,B_87] :
      ( v1_funct_2(k4_tmap_1(A_86,B_87),u1_struct_0(B_87),u1_struct_0(A_86))
      | ~ m1_pre_topc(B_87,A_86)
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_2098,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4','#skF_3','#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2088])).

tff(c_2118,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2098])).

tff(c_2121,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_2118])).

tff(c_2124,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_2121])).

tff(c_2126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2124])).

tff(c_2128,plain,(
    v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2098])).

tff(c_2127,plain,
    ( r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4','#skF_3','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2098])).

tff(c_2129,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2127])).

tff(c_2131,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2129,c_14])).

tff(c_2134,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2099,c_2128,c_2131])).

tff(c_2162,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_2134])).

tff(c_2165,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_2162])).

tff(c_2168,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_2165])).

tff(c_2170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2168])).

tff(c_2171,plain,(
    k4_tmap_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2134])).

tff(c_2176,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2171,c_54])).

tff(c_2182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_2176])).

tff(c_2183,plain,(
    r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4','#skF_3','#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2127])).

tff(c_520,plain,(
    ! [C_326] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5')
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_326,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_326) ) ),
    inference(splitRight,[status(thm)],[c_498])).

tff(c_556,plain,(
    ! [C_334] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_334,'#skF_5'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_334,'#skF_5')
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_334,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_334) ) ),
    inference(splitRight,[status(thm)],[c_498])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [A_234,B_235,C_236] :
      ( k1_funct_1(k4_tmap_1(A_234,B_235),C_236) = C_236
      | ~ r2_hidden(C_236,u1_struct_0(B_235))
      | ~ m1_subset_1(C_236,u1_struct_0(A_234))
      | ~ m1_pre_topc(B_235,A_234)
      | v2_struct_0(B_235)
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_162,plain,(
    ! [A_234,B_235,A_1] :
      ( k1_funct_1(k4_tmap_1(A_234,B_235),A_1) = A_1
      | ~ m1_subset_1(A_1,u1_struct_0(A_234))
      | ~ m1_pre_topc(B_235,A_234)
      | v2_struct_0(B_235)
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234)
      | v1_xboole_0(u1_struct_0(B_235))
      | ~ m1_subset_1(A_1,u1_struct_0(B_235)) ) ),
    inference(resolution,[status(thm)],[c_2,c_158])).

tff(c_560,plain,(
    ! [B_235,C_334] :
      ( k1_funct_1(k4_tmap_1('#skF_3',B_235),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_334,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_334,'#skF_5')
      | ~ m1_pre_topc(B_235,'#skF_3')
      | v2_struct_0(B_235)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | v1_xboole_0(u1_struct_0(B_235))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_334,'#skF_5'),u1_struct_0(B_235))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_334,'#skF_5')
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_334,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_334) ) ),
    inference(resolution,[status(thm)],[c_556,c_162])).

tff(c_569,plain,(
    ! [B_235,C_334] :
      ( k1_funct_1(k4_tmap_1('#skF_3',B_235),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_334,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_334,'#skF_5')
      | ~ m1_pre_topc(B_235,'#skF_3')
      | v2_struct_0(B_235)
      | v2_struct_0('#skF_3')
      | v1_xboole_0(u1_struct_0(B_235))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_334,'#skF_5'),u1_struct_0(B_235))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_334,'#skF_5')
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_334,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_560])).

tff(c_647,plain,(
    ! [B_343,C_344] :
      ( k1_funct_1(k4_tmap_1('#skF_3',B_343),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_344,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_344,'#skF_5')
      | ~ m1_pre_topc(B_343,'#skF_3')
      | v2_struct_0(B_343)
      | v1_xboole_0(u1_struct_0(B_343))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_344,'#skF_5'),u1_struct_0(B_343))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_344,'#skF_5')
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_344,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_344) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_569])).

tff(c_653,plain,(
    ! [C_326] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_3'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5')
      | ~ m1_pre_topc('#skF_3','#skF_3')
      | v2_struct_0('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5')
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_326,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_326) ) ),
    inference(resolution,[status(thm)],[c_520,c_647])).

tff(c_663,plain,(
    ! [C_326] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_3'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5')
      | ~ m1_pre_topc('#skF_3','#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5')
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_326,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_326) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_653])).

tff(c_710,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_663])).

tff(c_726,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_710])).

tff(c_730,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_726])).

tff(c_731,plain,(
    ! [C_326] :
      ( v1_xboole_0(u1_struct_0('#skF_3'))
      | k1_funct_1(k4_tmap_1('#skF_3','#skF_3'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5')
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_326,'#skF_5')
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_326,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_326) ) ),
    inference(splitRight,[status(thm)],[c_663])).

tff(c_778,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_731])).

tff(c_101,plain,(
    ! [B_205,A_206] :
      ( m1_subset_1(u1_struct_0(B_205),k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ m1_pre_topc(B_205,A_206)
      | ~ l1_pre_topc(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_4,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ v1_xboole_0(C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_104,plain,(
    ! [A_206,A_3,B_205] :
      ( ~ v1_xboole_0(u1_struct_0(A_206))
      | ~ r2_hidden(A_3,u1_struct_0(B_205))
      | ~ m1_pre_topc(B_205,A_206)
      | ~ l1_pre_topc(A_206) ) ),
    inference(resolution,[status(thm)],[c_101,c_4])).

tff(c_800,plain,(
    ! [A_3,B_205] :
      ( ~ r2_hidden(A_3,u1_struct_0(B_205))
      | ~ m1_pre_topc(B_205,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_778,c_104])).

tff(c_803,plain,(
    ! [A_3,B_205] :
      ( ~ r2_hidden(A_3,u1_struct_0(B_205))
      | ~ m1_pre_topc(B_205,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_800])).

tff(c_2207,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_2183,c_803])).

tff(c_2225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2207])).

tff(c_2242,plain,(
    ! [C_524] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_3'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_524,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_524,'#skF_5')
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_524,'#skF_5')
      | ~ m1_subset_1(C_524,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_524,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_524) ) ),
    inference(splitRight,[status(thm)],[c_731])).

tff(c_2250,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_3'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_2242])).

tff(c_2260,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_3'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_2250])).

tff(c_2261,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_3'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_54,c_2260])).

tff(c_2265,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2261])).

tff(c_2281,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_2265])).

tff(c_2284,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_2281])).

tff(c_2286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2284])).

tff(c_2288,plain,(
    v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2261])).

tff(c_2287,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | k1_funct_1(k4_tmap_1('#skF_3','#skF_3'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_2261])).

tff(c_2289,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2287])).

tff(c_2313,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_2289])).

tff(c_2316,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_2313])).

tff(c_2318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2316])).

tff(c_2320,plain,(
    v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2287])).

tff(c_2330,plain,(
    ! [D_544,E_543,B_546,C_545,A_542] :
      ( k3_tmap_1(A_542,B_546,C_545,D_544,E_543) = k2_partfun1(u1_struct_0(C_545),u1_struct_0(B_546),E_543,u1_struct_0(D_544))
      | ~ m1_pre_topc(D_544,C_545)
      | ~ m1_subset_1(E_543,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_545),u1_struct_0(B_546))))
      | ~ v1_funct_2(E_543,u1_struct_0(C_545),u1_struct_0(B_546))
      | ~ v1_funct_1(E_543)
      | ~ m1_pre_topc(D_544,A_542)
      | ~ m1_pre_topc(C_545,A_542)
      | ~ l1_pre_topc(B_546)
      | ~ v2_pre_topc(B_546)
      | v2_struct_0(B_546)
      | ~ l1_pre_topc(A_542)
      | ~ v2_pre_topc(A_542)
      | v2_struct_0(A_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_2336,plain,(
    ! [A_542,D_544] :
      ( k3_tmap_1(A_542,'#skF_3','#skF_4',D_544,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_544))
      | ~ m1_pre_topc(D_544,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_544,A_542)
      | ~ m1_pre_topc('#skF_4',A_542)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_542)
      | ~ v2_pre_topc(A_542)
      | v2_struct_0(A_542) ) ),
    inference(resolution,[status(thm)],[c_58,c_2330])).

tff(c_2341,plain,(
    ! [A_542,D_544] :
      ( k3_tmap_1(A_542,'#skF_3','#skF_4',D_544,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_544))
      | ~ m1_pre_topc(D_544,'#skF_4')
      | ~ m1_pre_topc(D_544,A_542)
      | ~ m1_pre_topc('#skF_4',A_542)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_542)
      | ~ v2_pre_topc(A_542)
      | v2_struct_0(A_542) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_62,c_60,c_2336])).

tff(c_2343,plain,(
    ! [A_547,D_548] :
      ( k3_tmap_1(A_547,'#skF_3','#skF_4',D_548,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_548))
      | ~ m1_pre_topc(D_548,'#skF_4')
      | ~ m1_pre_topc(D_548,A_547)
      | ~ m1_pre_topc('#skF_4',A_547)
      | ~ l1_pre_topc(A_547)
      | ~ v2_pre_topc(A_547)
      | v2_struct_0(A_547) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2341])).

tff(c_2347,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_521,c_2343])).

tff(c_2358,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_84,c_521,c_428,c_2347])).

tff(c_2359,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2358])).

tff(c_2368,plain,
    ( k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2359,c_324])).

tff(c_2375,plain,(
    k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_2368])).

tff(c_2509,plain,(
    ! [B_554,A_555,E_552,C_556,D_553] :
      ( m1_subset_1('#skF_2'(E_552,D_553,B_554,A_555,C_556),u1_struct_0(B_554))
      | r2_funct_2(u1_struct_0(C_556),u1_struct_0(A_555),k2_tmap_1(B_554,A_555,D_553,C_556),E_552)
      | ~ m1_subset_1(E_552,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_556),u1_struct_0(A_555))))
      | ~ v1_funct_2(E_552,u1_struct_0(C_556),u1_struct_0(A_555))
      | ~ v1_funct_1(E_552)
      | ~ m1_subset_1(D_553,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_554),u1_struct_0(A_555))))
      | ~ v1_funct_2(D_553,u1_struct_0(B_554),u1_struct_0(A_555))
      | ~ v1_funct_1(D_553)
      | ~ m1_pre_topc(C_556,B_554)
      | v2_struct_0(C_556)
      | ~ l1_pre_topc(B_554)
      | ~ v2_pre_topc(B_554)
      | v2_struct_0(B_554)
      | ~ l1_pre_topc(A_555)
      | ~ v2_pre_topc(A_555)
      | v2_struct_0(A_555) ) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_3495,plain,(
    ! [A_652,B_653,D_654,B_655] :
      ( m1_subset_1('#skF_2'(k4_tmap_1(A_652,B_653),D_654,B_655,A_652,B_653),u1_struct_0(B_655))
      | r2_funct_2(u1_struct_0(B_653),u1_struct_0(A_652),k2_tmap_1(B_655,A_652,D_654,B_653),k4_tmap_1(A_652,B_653))
      | ~ v1_funct_2(k4_tmap_1(A_652,B_653),u1_struct_0(B_653),u1_struct_0(A_652))
      | ~ v1_funct_1(k4_tmap_1(A_652,B_653))
      | ~ m1_subset_1(D_654,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_655),u1_struct_0(A_652))))
      | ~ v1_funct_2(D_654,u1_struct_0(B_655),u1_struct_0(A_652))
      | ~ v1_funct_1(D_654)
      | ~ m1_pre_topc(B_653,B_655)
      | v2_struct_0(B_653)
      | ~ l1_pre_topc(B_655)
      | ~ v2_pre_topc(B_655)
      | v2_struct_0(B_655)
      | ~ m1_pre_topc(B_653,A_652)
      | ~ l1_pre_topc(A_652)
      | ~ v2_pre_topc(A_652)
      | v2_struct_0(A_652) ) ),
    inference(resolution,[status(thm)],[c_32,c_2509])).

tff(c_3509,plain,
    ( m1_subset_1('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4','#skF_3','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2375,c_3495])).

tff(c_3516,plain,
    ( m1_subset_1('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4','#skF_3','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_100,c_84,c_521,c_62,c_60,c_58,c_2288,c_2320,c_3509])).

tff(c_3517,plain,
    ( m1_subset_1('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4','#skF_3','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_3516])).

tff(c_3518,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3517])).

tff(c_3520,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3518,c_14])).

tff(c_3523,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2288,c_2320,c_3520])).

tff(c_3524,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_3523])).

tff(c_3545,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_3524])).

tff(c_3548,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_3545])).

tff(c_3550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3548])).

tff(c_3551,plain,(
    k4_tmap_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3523])).

tff(c_3559,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3551,c_54])).

tff(c_3565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_3559])).

tff(c_3567,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3517])).

tff(c_2692,plain,(
    ! [E_569,C_573,D_570,B_571,A_572] :
      ( r2_hidden('#skF_2'(E_569,D_570,B_571,A_572,C_573),u1_struct_0(C_573))
      | r2_funct_2(u1_struct_0(C_573),u1_struct_0(A_572),k2_tmap_1(B_571,A_572,D_570,C_573),E_569)
      | ~ m1_subset_1(E_569,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_573),u1_struct_0(A_572))))
      | ~ v1_funct_2(E_569,u1_struct_0(C_573),u1_struct_0(A_572))
      | ~ v1_funct_1(E_569)
      | ~ m1_subset_1(D_570,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_571),u1_struct_0(A_572))))
      | ~ v1_funct_2(D_570,u1_struct_0(B_571),u1_struct_0(A_572))
      | ~ v1_funct_1(D_570)
      | ~ m1_pre_topc(C_573,B_571)
      | v2_struct_0(C_573)
      | ~ l1_pre_topc(B_571)
      | ~ v2_pre_topc(B_571)
      | v2_struct_0(B_571)
      | ~ l1_pre_topc(A_572)
      | ~ v2_pre_topc(A_572)
      | v2_struct_0(A_572) ) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_3602,plain,(
    ! [A_659,B_660,D_661,B_662] :
      ( r2_hidden('#skF_2'(k4_tmap_1(A_659,B_660),D_661,B_662,A_659,B_660),u1_struct_0(B_660))
      | r2_funct_2(u1_struct_0(B_660),u1_struct_0(A_659),k2_tmap_1(B_662,A_659,D_661,B_660),k4_tmap_1(A_659,B_660))
      | ~ v1_funct_2(k4_tmap_1(A_659,B_660),u1_struct_0(B_660),u1_struct_0(A_659))
      | ~ v1_funct_1(k4_tmap_1(A_659,B_660))
      | ~ m1_subset_1(D_661,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_662),u1_struct_0(A_659))))
      | ~ v1_funct_2(D_661,u1_struct_0(B_662),u1_struct_0(A_659))
      | ~ v1_funct_1(D_661)
      | ~ m1_pre_topc(B_660,B_662)
      | v2_struct_0(B_660)
      | ~ l1_pre_topc(B_662)
      | ~ v2_pre_topc(B_662)
      | v2_struct_0(B_662)
      | ~ m1_pre_topc(B_660,A_659)
      | ~ l1_pre_topc(A_659)
      | ~ v2_pre_topc(A_659)
      | v2_struct_0(A_659) ) ),
    inference(resolution,[status(thm)],[c_32,c_2692])).

tff(c_3607,plain,
    ( r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4','#skF_3','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2375,c_3602])).

tff(c_3610,plain,
    ( r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4','#skF_3','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_100,c_84,c_521,c_62,c_60,c_58,c_2288,c_2320,c_3607])).

tff(c_3611,plain,(
    r2_hidden('#skF_2'(k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4','#skF_3','#skF_4'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_3567,c_3610])).

tff(c_106,plain,(
    ! [D_207] :
      ( k1_funct_1('#skF_5',D_207) = D_207
      | ~ r2_hidden(D_207,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_207,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_357])).

tff(c_111,plain,(
    ! [A_1] :
      ( k1_funct_1('#skF_5',A_1) = A_1
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2,c_106])).

tff(c_129,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_132,plain,(
    ! [A_3,B_205] :
      ( ~ r2_hidden(A_3,u1_struct_0(B_205))
      | ~ m1_pre_topc(B_205,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_129,c_104])).

tff(c_135,plain,(
    ! [A_3,B_205] :
      ( ~ r2_hidden(A_3,u1_struct_0(B_205))
      | ~ m1_pre_topc(B_205,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_132])).

tff(c_3620,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_3611,c_135])).

tff(c_3632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_3620])).

tff(c_3633,plain,(
    ! [A_1] :
      ( k1_funct_1('#skF_5',A_1) = A_1
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_3714,plain,(
    ! [C_699] :
      ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_699,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_699,'#skF_5')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_699,'#skF_5'),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_699,'#skF_5')
      | ~ m1_subset_1(C_699,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_699,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_699) ) ),
    inference(resolution,[status(thm)],[c_3704,c_3633])).

tff(c_3720,plain,(
    ! [C_699] :
      ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_699,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_699,'#skF_5')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_699,'#skF_5'),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_3')
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_699,'#skF_5')
      | ~ m1_subset_1(C_699,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_699,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_699) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_3714])).

tff(c_3838,plain,(
    ! [C_751] :
      ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_751,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_751,'#skF_5')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_751,'#skF_5'),u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_751,'#skF_5')
      | ~ m1_subset_1(C_751,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_751,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_751) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3720])).

tff(c_3929,plain,(
    ! [C_754] :
      ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_754,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_754,'#skF_5')
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_754,'#skF_5')
      | ~ m1_subset_1(C_754,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_754,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_754) ) ),
    inference(resolution,[status(thm)],[c_3678,c_3838])).

tff(c_3937,plain,
    ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_3929])).

tff(c_3947,plain,
    ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_3937])).

tff(c_3948,plain,
    ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_54,c_3947])).

tff(c_3985,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3948])).

tff(c_4016,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_3985])).

tff(c_4019,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_4016])).

tff(c_4021,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4019])).

tff(c_4023,plain,(
    v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3948])).

tff(c_4022,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3948])).

tff(c_4148,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4022])).

tff(c_4151,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_4148])).

tff(c_4154,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_4151])).

tff(c_4156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4154])).

tff(c_4158,plain,(
    v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4022])).

tff(c_4157,plain,(
    k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_4022])).

tff(c_3634,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_3722,plain,(
    ! [E_702,A_701,C_703,B_705,D_704] :
      ( v1_funct_1(k3_tmap_1(A_701,B_705,C_703,D_704,E_702))
      | ~ m1_subset_1(E_702,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_703),u1_struct_0(B_705))))
      | ~ v1_funct_2(E_702,u1_struct_0(C_703),u1_struct_0(B_705))
      | ~ v1_funct_1(E_702)
      | ~ m1_pre_topc(D_704,A_701)
      | ~ m1_pre_topc(C_703,A_701)
      | ~ l1_pre_topc(B_705)
      | ~ v2_pre_topc(B_705)
      | v2_struct_0(B_705)
      | ~ l1_pre_topc(A_701)
      | ~ v2_pre_topc(A_701)
      | v2_struct_0(A_701) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_3726,plain,(
    ! [A_701,D_704] :
      ( v1_funct_1(k3_tmap_1(A_701,'#skF_3','#skF_4',D_704,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_704,A_701)
      | ~ m1_pre_topc('#skF_4',A_701)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_701)
      | ~ v2_pre_topc(A_701)
      | v2_struct_0(A_701) ) ),
    inference(resolution,[status(thm)],[c_58,c_3722])).

tff(c_3730,plain,(
    ! [A_701,D_704] :
      ( v1_funct_1(k3_tmap_1(A_701,'#skF_3','#skF_4',D_704,'#skF_5'))
      | ~ m1_pre_topc(D_704,A_701)
      | ~ m1_pre_topc('#skF_4',A_701)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_701)
      | ~ v2_pre_topc(A_701)
      | v2_struct_0(A_701) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_62,c_60,c_3726])).

tff(c_3731,plain,(
    ! [A_701,D_704] :
      ( v1_funct_1(k3_tmap_1(A_701,'#skF_3','#skF_4',D_704,'#skF_5'))
      | ~ m1_pre_topc(D_704,A_701)
      | ~ m1_pre_topc('#skF_4',A_701)
      | ~ l1_pre_topc(A_701)
      | ~ v2_pre_topc(A_701)
      | v2_struct_0(A_701) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3730])).

tff(c_3777,plain,(
    ! [A_730,D_733,B_734,C_732,E_731] :
      ( v1_funct_2(k3_tmap_1(A_730,B_734,C_732,D_733,E_731),u1_struct_0(D_733),u1_struct_0(B_734))
      | ~ m1_subset_1(E_731,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_732),u1_struct_0(B_734))))
      | ~ v1_funct_2(E_731,u1_struct_0(C_732),u1_struct_0(B_734))
      | ~ v1_funct_1(E_731)
      | ~ m1_pre_topc(D_733,A_730)
      | ~ m1_pre_topc(C_732,A_730)
      | ~ l1_pre_topc(B_734)
      | ~ v2_pre_topc(B_734)
      | v2_struct_0(B_734)
      | ~ l1_pre_topc(A_730)
      | ~ v2_pre_topc(A_730)
      | v2_struct_0(A_730) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_3781,plain,(
    ! [A_730,D_733] :
      ( v1_funct_2(k3_tmap_1(A_730,'#skF_3','#skF_4',D_733,'#skF_5'),u1_struct_0(D_733),u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_733,A_730)
      | ~ m1_pre_topc('#skF_4',A_730)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_730)
      | ~ v2_pre_topc(A_730)
      | v2_struct_0(A_730) ) ),
    inference(resolution,[status(thm)],[c_58,c_3777])).

tff(c_3785,plain,(
    ! [A_730,D_733] :
      ( v1_funct_2(k3_tmap_1(A_730,'#skF_3','#skF_4',D_733,'#skF_5'),u1_struct_0(D_733),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_733,A_730)
      | ~ m1_pre_topc('#skF_4',A_730)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_730)
      | ~ v2_pre_topc(A_730)
      | v2_struct_0(A_730) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_62,c_60,c_3781])).

tff(c_3786,plain,(
    ! [A_730,D_733] :
      ( v1_funct_2(k3_tmap_1(A_730,'#skF_3','#skF_4',D_733,'#skF_5'),u1_struct_0(D_733),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_733,A_730)
      | ~ m1_pre_topc('#skF_4',A_730)
      | ~ l1_pre_topc(A_730)
      | ~ v2_pre_topc(A_730)
      | v2_struct_0(A_730) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3785])).

tff(c_3761,plain,(
    ! [C_725,B_726,D_727,A_728] :
      ( r2_funct_2(u1_struct_0(C_725),u1_struct_0(B_726),D_727,k3_tmap_1(A_728,B_726,C_725,C_725,D_727))
      | ~ m1_subset_1(D_727,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_725),u1_struct_0(B_726))))
      | ~ v1_funct_2(D_727,u1_struct_0(C_725),u1_struct_0(B_726))
      | ~ v1_funct_1(D_727)
      | ~ m1_pre_topc(C_725,A_728)
      | v2_struct_0(C_725)
      | ~ l1_pre_topc(B_726)
      | ~ v2_pre_topc(B_726)
      | v2_struct_0(B_726)
      | ~ l1_pre_topc(A_728)
      | ~ v2_pre_topc(A_728)
      | v2_struct_0(A_728) ) ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_3765,plain,(
    ! [A_728] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_728,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_728)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_728)
      | ~ v2_pre_topc(A_728)
      | v2_struct_0(A_728) ) ),
    inference(resolution,[status(thm)],[c_58,c_3761])).

tff(c_3769,plain,(
    ! [A_728] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_728,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_728)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_728)
      | ~ v2_pre_topc(A_728)
      | v2_struct_0(A_728) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_62,c_60,c_3765])).

tff(c_3771,plain,(
    ! [A_729] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_729,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_729)
      | ~ l1_pre_topc(A_729)
      | ~ v2_pre_topc(A_729)
      | v2_struct_0(A_729) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_3769])).

tff(c_3773,plain,(
    ! [A_729] :
      ( k3_tmap_1(A_729,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_subset_1(k3_tmap_1(A_729,'#skF_3','#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k3_tmap_1(A_729,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_729,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_729)
      | ~ l1_pre_topc(A_729)
      | ~ v2_pre_topc(A_729)
      | v2_struct_0(A_729) ) ),
    inference(resolution,[status(thm)],[c_3771,c_14])).

tff(c_3823,plain,(
    ! [A_749] :
      ( k3_tmap_1(A_749,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_subset_1(k3_tmap_1(A_749,'#skF_3','#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k3_tmap_1(A_749,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_749,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_749)
      | ~ l1_pre_topc(A_749)
      | ~ v2_pre_topc(A_749)
      | v2_struct_0(A_749) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_3773])).

tff(c_3827,plain,(
    ! [A_81] :
      ( k3_tmap_1(A_81,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_81,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_81,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_81)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_26,c_3823])).

tff(c_3830,plain,(
    ! [A_81] :
      ( k3_tmap_1(A_81,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_81,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_81,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_81)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_62,c_60,c_58,c_3827])).

tff(c_3832,plain,(
    ! [A_750] :
      ( k3_tmap_1(A_750,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_750,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_750,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_750)
      | ~ l1_pre_topc(A_750)
      | ~ v2_pre_topc(A_750)
      | v2_struct_0(A_750) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3830])).

tff(c_3851,plain,(
    ! [A_752] :
      ( k3_tmap_1(A_752,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_1(k3_tmap_1(A_752,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_752)
      | ~ l1_pre_topc(A_752)
      | ~ v2_pre_topc(A_752)
      | v2_struct_0(A_752) ) ),
    inference(resolution,[status(thm)],[c_3786,c_3832])).

tff(c_3857,plain,(
    ! [A_753] :
      ( k3_tmap_1(A_753,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_pre_topc('#skF_4',A_753)
      | ~ l1_pre_topc(A_753)
      | ~ v2_pre_topc(A_753)
      | v2_struct_0(A_753) ) ),
    inference(resolution,[status(thm)],[c_3731,c_3851])).

tff(c_3864,plain,
    ( k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_3857])).

tff(c_3871,plain,
    ( k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3864])).

tff(c_3872,plain,(
    k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3871])).

tff(c_3952,plain,(
    ! [D_757,B_759,A_755,E_756,C_758] :
      ( k3_tmap_1(A_755,B_759,C_758,D_757,E_756) = k2_partfun1(u1_struct_0(C_758),u1_struct_0(B_759),E_756,u1_struct_0(D_757))
      | ~ m1_pre_topc(D_757,C_758)
      | ~ m1_subset_1(E_756,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_758),u1_struct_0(B_759))))
      | ~ v1_funct_2(E_756,u1_struct_0(C_758),u1_struct_0(B_759))
      | ~ v1_funct_1(E_756)
      | ~ m1_pre_topc(D_757,A_755)
      | ~ m1_pre_topc(C_758,A_755)
      | ~ l1_pre_topc(B_759)
      | ~ v2_pre_topc(B_759)
      | v2_struct_0(B_759)
      | ~ l1_pre_topc(A_755)
      | ~ v2_pre_topc(A_755)
      | v2_struct_0(A_755) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_3958,plain,(
    ! [A_755,D_757] :
      ( k3_tmap_1(A_755,'#skF_3','#skF_4',D_757,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_757))
      | ~ m1_pre_topc(D_757,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_757,A_755)
      | ~ m1_pre_topc('#skF_4',A_755)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_755)
      | ~ v2_pre_topc(A_755)
      | v2_struct_0(A_755) ) ),
    inference(resolution,[status(thm)],[c_58,c_3952])).

tff(c_3963,plain,(
    ! [A_755,D_757] :
      ( k3_tmap_1(A_755,'#skF_3','#skF_4',D_757,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_757))
      | ~ m1_pre_topc(D_757,'#skF_4')
      | ~ m1_pre_topc(D_757,A_755)
      | ~ m1_pre_topc('#skF_4',A_755)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_755)
      | ~ v2_pre_topc(A_755)
      | v2_struct_0(A_755) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_62,c_60,c_3958])).

tff(c_3965,plain,(
    ! [A_760,D_761] :
      ( k3_tmap_1(A_760,'#skF_3','#skF_4',D_761,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_761))
      | ~ m1_pre_topc(D_761,'#skF_4')
      | ~ m1_pre_topc(D_761,A_760)
      | ~ m1_pre_topc('#skF_4',A_760)
      | ~ l1_pre_topc(A_760)
      | ~ v2_pre_topc(A_760)
      | v2_struct_0(A_760) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3963])).

tff(c_3969,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_3965])).

tff(c_3973,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_3872,c_3969])).

tff(c_3974,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3973])).

tff(c_3975,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3974])).

tff(c_3978,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_3975])).

tff(c_3982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3978])).

tff(c_3984,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_3974])).

tff(c_4591,plain,(
    ! [C_809,A_810,A_811] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_809,'#skF_5'),u1_struct_0(A_810))
      | ~ m1_pre_topc(A_811,A_810)
      | ~ l1_pre_topc(A_810)
      | v2_struct_0(A_810)
      | ~ m1_pre_topc('#skF_4',A_811)
      | ~ l1_pre_topc(A_811)
      | v2_struct_0(A_811)
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_809,'#skF_5')
      | ~ m1_subset_1(C_809,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_809,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_809) ) ),
    inference(resolution,[status(thm)],[c_3704,c_20])).

tff(c_4597,plain,(
    ! [C_809] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_809,'#skF_5'),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_809,'#skF_5')
      | ~ m1_subset_1(C_809,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_809,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_809) ) ),
    inference(resolution,[status(thm)],[c_64,c_4591])).

tff(c_4605,plain,(
    ! [C_809] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_809,'#skF_5'),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_809,'#skF_5')
      | ~ m1_subset_1(C_809,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_809,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_809) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3984,c_68,c_4597])).

tff(c_4607,plain,(
    ! [C_812] :
      ( m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_812,'#skF_5'),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_812,'#skF_5')
      | ~ m1_subset_1(C_812,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_812,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_812) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_72,c_4605])).

tff(c_3652,plain,(
    ! [A_677,B_678,C_679] :
      ( k1_funct_1(k4_tmap_1(A_677,B_678),C_679) = C_679
      | ~ r2_hidden(C_679,u1_struct_0(B_678))
      | ~ m1_subset_1(C_679,u1_struct_0(A_677))
      | ~ m1_pre_topc(B_678,A_677)
      | v2_struct_0(B_678)
      | ~ l1_pre_topc(A_677)
      | ~ v2_pre_topc(A_677)
      | v2_struct_0(A_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_3656,plain,(
    ! [A_677,B_678,A_1] :
      ( k1_funct_1(k4_tmap_1(A_677,B_678),A_1) = A_1
      | ~ m1_subset_1(A_1,u1_struct_0(A_677))
      | ~ m1_pre_topc(B_678,A_677)
      | v2_struct_0(B_678)
      | ~ l1_pre_topc(A_677)
      | ~ v2_pre_topc(A_677)
      | v2_struct_0(A_677)
      | v1_xboole_0(u1_struct_0(B_678))
      | ~ m1_subset_1(A_1,u1_struct_0(B_678)) ) ),
    inference(resolution,[status(thm)],[c_2,c_3652])).

tff(c_4611,plain,(
    ! [B_678,C_812] :
      ( k1_funct_1(k4_tmap_1('#skF_3',B_678),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_812,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_812,'#skF_5')
      | ~ m1_pre_topc(B_678,'#skF_3')
      | v2_struct_0(B_678)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | v1_xboole_0(u1_struct_0(B_678))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_812,'#skF_5'),u1_struct_0(B_678))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_812,'#skF_5')
      | ~ m1_subset_1(C_812,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_812,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_812) ) ),
    inference(resolution,[status(thm)],[c_4607,c_3656])).

tff(c_4620,plain,(
    ! [B_678,C_812] :
      ( k1_funct_1(k4_tmap_1('#skF_3',B_678),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_812,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_812,'#skF_5')
      | ~ m1_pre_topc(B_678,'#skF_3')
      | v2_struct_0(B_678)
      | v2_struct_0('#skF_3')
      | v1_xboole_0(u1_struct_0(B_678))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_812,'#skF_5'),u1_struct_0(B_678))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_812,'#skF_5')
      | ~ m1_subset_1(C_812,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_812,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_812) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_4611])).

tff(c_5282,plain,(
    ! [B_886,C_887] :
      ( k1_funct_1(k4_tmap_1('#skF_3',B_886),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_887,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_887,'#skF_5')
      | ~ m1_pre_topc(B_886,'#skF_3')
      | v2_struct_0(B_886)
      | v1_xboole_0(u1_struct_0(B_886))
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_887,'#skF_5'),u1_struct_0(B_886))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_887,'#skF_5')
      | ~ m1_subset_1(C_887,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_887,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_887) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4620])).

tff(c_5294,plain,(
    ! [C_691] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_691,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_691,'#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_691,'#skF_5')
      | ~ m1_subset_1(C_691,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_691,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_691) ) ),
    inference(resolution,[status(thm)],[c_3678,c_5282])).

tff(c_5302,plain,(
    ! [C_691] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_691,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_691,'#skF_5')
      | v2_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_691,'#skF_5')
      | ~ m1_subset_1(C_691,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_691,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_691) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5294])).

tff(c_5304,plain,(
    ! [C_888] :
      ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_888,'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_888,'#skF_5')
      | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),C_888,'#skF_5')
      | ~ m1_subset_1(C_888,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_888,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_888) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3634,c_66,c_5302])).

tff(c_5324,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_5304])).

tff(c_5346,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_4023,c_4158,c_5324])).

tff(c_5347,plain,(
    k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) = '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_54,c_5346])).

tff(c_8,plain,(
    ! [D_14,A_6,B_7,C_8] :
      ( k1_funct_1(D_14,'#skF_1'(A_6,B_7,C_8,D_14)) != k1_funct_1(C_8,'#skF_1'(A_6,B_7,C_8,D_14))
      | r2_funct_2(A_6,B_7,C_8,D_14)
      | ~ m1_subset_1(D_14,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7)))
      | ~ v1_funct_2(D_14,A_6,B_7)
      | ~ v1_funct_1(D_14)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7)))
      | ~ v1_funct_2(C_8,A_6,B_7)
      | ~ v1_funct_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5353,plain,
    ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')) != '#skF_1'(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5347,c_8])).

tff(c_5357,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5')
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4023,c_4158,c_62,c_60,c_58,c_4157,c_5353])).

tff(c_5358,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5357])).

tff(c_5362,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_5358])).

tff(c_5365,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_5362])).

tff(c_5367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:11:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.17/3.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.17/3.14  
% 9.17/3.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.17/3.14  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 9.17/3.14  
% 9.17/3.14  %Foreground sorts:
% 9.17/3.14  
% 9.17/3.14  
% 9.17/3.14  %Background operators:
% 9.17/3.14  
% 9.17/3.14  
% 9.17/3.14  %Foreground operators:
% 9.17/3.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.17/3.14  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 9.17/3.14  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 9.17/3.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.17/3.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.17/3.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.17/3.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 9.17/3.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.17/3.14  tff('#skF_5', type, '#skF_5': $i).
% 9.17/3.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.17/3.14  tff('#skF_3', type, '#skF_3': $i).
% 9.17/3.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.17/3.14  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.17/3.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.17/3.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.17/3.14  tff('#skF_4', type, '#skF_4': $i).
% 9.17/3.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.17/3.14  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.17/3.14  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.17/3.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.17/3.14  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 9.17/3.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 9.17/3.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.17/3.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.17/3.14  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 9.17/3.14  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 9.17/3.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.17/3.14  
% 9.58/3.19  tff(f_357, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 9.58/3.19  tff(f_210, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 9.58/3.19  tff(f_58, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_2)).
% 9.58/3.19  tff(f_106, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 9.58/3.19  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.58/3.19  tff(f_221, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 9.58/3.19  tff(f_74, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 9.58/3.19  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 9.58/3.19  tff(f_195, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 9.58/3.19  tff(f_295, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 9.58/3.19  tff(f_165, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 9.58/3.19  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 9.58/3.19  tff(f_265, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => ((![F]: (m1_subset_1(F, u1_struct_0(B)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(B), u1_struct_0(A), D, F) = k1_funct_1(E, F))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tmap_1)).
% 9.58/3.19  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 9.58/3.19  tff(f_327, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 9.58/3.19  tff(f_217, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 9.58/3.19  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 9.58/3.19  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_357])).
% 9.58/3.19  tff(c_70, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_357])).
% 9.58/3.19  tff(c_68, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_357])).
% 9.58/3.19  tff(c_64, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_357])).
% 9.58/3.19  tff(c_32, plain, (![A_86, B_87]: (m1_subset_1(k4_tmap_1(A_86, B_87), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_87), u1_struct_0(A_86)))) | ~m1_pre_topc(B_87, A_86) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_210])).
% 9.58/3.19  tff(c_54, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_357])).
% 9.58/3.19  tff(c_36, plain, (![A_86, B_87]: (v1_funct_1(k4_tmap_1(A_86, B_87)) | ~m1_pre_topc(B_87, A_86) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_210])).
% 9.58/3.19  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_357])).
% 9.58/3.19  tff(c_60, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_357])).
% 9.58/3.19  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_357])).
% 9.58/3.19  tff(c_3670, plain, (![A_689, B_690, C_691, D_692]: (m1_subset_1('#skF_1'(A_689, B_690, C_691, D_692), A_689) | r2_funct_2(A_689, B_690, C_691, D_692) | ~m1_subset_1(D_692, k1_zfmisc_1(k2_zfmisc_1(A_689, B_690))) | ~v1_funct_2(D_692, A_689, B_690) | ~v1_funct_1(D_692) | ~m1_subset_1(C_691, k1_zfmisc_1(k2_zfmisc_1(A_689, B_690))) | ~v1_funct_2(C_691, A_689, B_690) | ~v1_funct_1(C_691))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.58/3.19  tff(c_3674, plain, (![C_691]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_691, '#skF_5'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_691, '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(C_691, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_691, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_691))), inference(resolution, [status(thm)], [c_58, c_3670])).
% 9.58/3.19  tff(c_3678, plain, (![C_691]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_691, '#skF_5'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_691, '#skF_5') | ~m1_subset_1(C_691, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_691, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_691))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_3674])).
% 9.58/3.19  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_357])).
% 9.58/3.19  tff(c_3679, plain, (![C_693]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_693, '#skF_5'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_693, '#skF_5') | ~m1_subset_1(C_693, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_693, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_693))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_3674])).
% 9.58/3.19  tff(c_20, plain, (![C_34, A_28, B_32]: (m1_subset_1(C_34, u1_struct_0(A_28)) | ~m1_subset_1(C_34, u1_struct_0(B_32)) | ~m1_pre_topc(B_32, A_28) | v2_struct_0(B_32) | ~l1_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.58/3.19  tff(c_3683, plain, (![C_693, A_28]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_693, '#skF_5'), u1_struct_0(A_28)) | ~m1_pre_topc('#skF_4', A_28) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_28) | v2_struct_0(A_28) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_693, '#skF_5') | ~m1_subset_1(C_693, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_693, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_693))), inference(resolution, [status(thm)], [c_3679, c_20])).
% 9.58/3.19  tff(c_3704, plain, (![C_699, A_700]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_699, '#skF_5'), u1_struct_0(A_700)) | ~m1_pre_topc('#skF_4', A_700) | ~l1_pre_topc(A_700) | v2_struct_0(A_700) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_699, '#skF_5') | ~m1_subset_1(C_699, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_699, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_699))), inference(negUnitSimplification, [status(thm)], [c_66, c_3683])).
% 9.58/3.19  tff(c_74, plain, (![B_196, A_197]: (l1_pre_topc(B_196) | ~m1_pre_topc(B_196, A_197) | ~l1_pre_topc(A_197))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.58/3.19  tff(c_80, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_74])).
% 9.58/3.19  tff(c_84, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_80])).
% 9.58/3.19  tff(c_40, plain, (![A_91]: (m1_pre_topc(A_91, A_91) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_221])).
% 9.58/3.19  tff(c_176, plain, (![A_246, B_247, C_248, D_249]: (m1_subset_1('#skF_1'(A_246, B_247, C_248, D_249), A_246) | r2_funct_2(A_246, B_247, C_248, D_249) | ~m1_subset_1(D_249, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))) | ~v1_funct_2(D_249, A_246, B_247) | ~v1_funct_1(D_249) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))) | ~v1_funct_2(C_248, A_246, B_247) | ~v1_funct_1(C_248))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.58/3.19  tff(c_180, plain, (![C_248]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_248, '#skF_5'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_248, '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_248, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_248))), inference(resolution, [status(thm)], [c_58, c_176])).
% 9.58/3.19  tff(c_185, plain, (![C_250]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_250, '#skF_5'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_250, '#skF_5') | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_250, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_250))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_180])).
% 9.58/3.19  tff(c_192, plain, (![C_250, A_28]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_250, '#skF_5'), u1_struct_0(A_28)) | ~m1_pre_topc('#skF_4', A_28) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_28) | v2_struct_0(A_28) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_250, '#skF_5') | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_250, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_250))), inference(resolution, [status(thm)], [c_185, c_20])).
% 9.58/3.19  tff(c_215, plain, (![C_256, A_257]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_256, '#skF_5'), u1_struct_0(A_257)) | ~m1_pre_topc('#skF_4', A_257) | ~l1_pre_topc(A_257) | v2_struct_0(A_257) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_256, '#skF_5') | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_256, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_256))), inference(negUnitSimplification, [status(thm)], [c_66, c_192])).
% 9.58/3.19  tff(c_489, plain, (![C_326, A_327, A_328]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5'), u1_struct_0(A_327)) | ~m1_pre_topc(A_328, A_327) | ~l1_pre_topc(A_327) | v2_struct_0(A_327) | ~m1_pre_topc('#skF_4', A_328) | ~l1_pre_topc(A_328) | v2_struct_0(A_328) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5') | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_326, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_326))), inference(resolution, [status(thm)], [c_215, c_20])).
% 9.58/3.19  tff(c_493, plain, (![C_326]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5'), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5') | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_326, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_326))), inference(resolution, [status(thm)], [c_64, c_489])).
% 9.58/3.19  tff(c_497, plain, (![C_326]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5') | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_326, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_326))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_68, c_493])).
% 9.58/3.19  tff(c_498, plain, (![C_326]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_4') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5') | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_326, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_326))), inference(negUnitSimplification, [status(thm)], [c_66, c_72, c_497])).
% 9.58/3.19  tff(c_499, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_498])).
% 9.58/3.19  tff(c_515, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_40, c_499])).
% 9.58/3.19  tff(c_519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_515])).
% 9.58/3.19  tff(c_521, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_498])).
% 9.58/3.19  tff(c_143, plain, (![A_224, B_225, D_226]: (r2_funct_2(A_224, B_225, D_226, D_226) | ~m1_subset_1(D_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))) | ~v1_funct_2(D_226, A_224, B_225) | ~v1_funct_1(D_226))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.58/3.19  tff(c_145, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_143])).
% 9.58/3.19  tff(c_148, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_145])).
% 9.58/3.19  tff(c_90, plain, (![B_203, A_204]: (v2_pre_topc(B_203) | ~m1_pre_topc(B_203, A_204) | ~l1_pre_topc(A_204) | ~v2_pre_topc(A_204))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.58/3.19  tff(c_96, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_90])).
% 9.58/3.19  tff(c_100, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_96])).
% 9.58/3.19  tff(c_295, plain, (![A_274, B_278, E_275, D_277, C_276]: (v1_funct_1(k3_tmap_1(A_274, B_278, C_276, D_277, E_275)) | ~m1_subset_1(E_275, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_276), u1_struct_0(B_278)))) | ~v1_funct_2(E_275, u1_struct_0(C_276), u1_struct_0(B_278)) | ~v1_funct_1(E_275) | ~m1_pre_topc(D_277, A_274) | ~m1_pre_topc(C_276, A_274) | ~l1_pre_topc(B_278) | ~v2_pre_topc(B_278) | v2_struct_0(B_278) | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.58/3.19  tff(c_299, plain, (![A_274, D_277]: (v1_funct_1(k3_tmap_1(A_274, '#skF_3', '#skF_4', D_277, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_277, A_274) | ~m1_pre_topc('#skF_4', A_274) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(resolution, [status(thm)], [c_58, c_295])).
% 9.58/3.19  tff(c_303, plain, (![A_274, D_277]: (v1_funct_1(k3_tmap_1(A_274, '#skF_3', '#skF_4', D_277, '#skF_5')) | ~m1_pre_topc(D_277, A_274) | ~m1_pre_topc('#skF_4', A_274) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_62, c_60, c_299])).
% 9.58/3.19  tff(c_304, plain, (![A_274, D_277]: (v1_funct_1(k3_tmap_1(A_274, '#skF_3', '#skF_4', D_277, '#skF_5')) | ~m1_pre_topc(D_277, A_274) | ~m1_pre_topc('#skF_4', A_274) | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(negUnitSimplification, [status(thm)], [c_72, c_303])).
% 9.58/3.19  tff(c_334, plain, (![D_301, E_299, B_302, C_300, A_298]: (v1_funct_2(k3_tmap_1(A_298, B_302, C_300, D_301, E_299), u1_struct_0(D_301), u1_struct_0(B_302)) | ~m1_subset_1(E_299, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_300), u1_struct_0(B_302)))) | ~v1_funct_2(E_299, u1_struct_0(C_300), u1_struct_0(B_302)) | ~v1_funct_1(E_299) | ~m1_pre_topc(D_301, A_298) | ~m1_pre_topc(C_300, A_298) | ~l1_pre_topc(B_302) | ~v2_pre_topc(B_302) | v2_struct_0(B_302) | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298) | v2_struct_0(A_298))), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.58/3.19  tff(c_338, plain, (![A_298, D_301]: (v1_funct_2(k3_tmap_1(A_298, '#skF_3', '#skF_4', D_301, '#skF_5'), u1_struct_0(D_301), u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_301, A_298) | ~m1_pre_topc('#skF_4', A_298) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298) | v2_struct_0(A_298))), inference(resolution, [status(thm)], [c_58, c_334])).
% 9.58/3.19  tff(c_342, plain, (![A_298, D_301]: (v1_funct_2(k3_tmap_1(A_298, '#skF_3', '#skF_4', D_301, '#skF_5'), u1_struct_0(D_301), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_301, A_298) | ~m1_pre_topc('#skF_4', A_298) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298) | v2_struct_0(A_298))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_62, c_60, c_338])).
% 9.58/3.19  tff(c_343, plain, (![A_298, D_301]: (v1_funct_2(k3_tmap_1(A_298, '#skF_3', '#skF_4', D_301, '#skF_5'), u1_struct_0(D_301), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_301, A_298) | ~m1_pre_topc('#skF_4', A_298) | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298) | v2_struct_0(A_298))), inference(negUnitSimplification, [status(thm)], [c_72, c_342])).
% 9.58/3.19  tff(c_26, plain, (![A_81, D_84, B_82, E_85, C_83]: (m1_subset_1(k3_tmap_1(A_81, B_82, C_83, D_84, E_85), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_84), u1_struct_0(B_82)))) | ~m1_subset_1(E_85, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_83), u1_struct_0(B_82)))) | ~v1_funct_2(E_85, u1_struct_0(C_83), u1_struct_0(B_82)) | ~v1_funct_1(E_85) | ~m1_pre_topc(D_84, A_81) | ~m1_pre_topc(C_83, A_81) | ~l1_pre_topc(B_82) | ~v2_pre_topc(B_82) | v2_struct_0(B_82) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.58/3.19  tff(c_345, plain, (![C_305, B_306, D_307, A_308]: (r2_funct_2(u1_struct_0(C_305), u1_struct_0(B_306), D_307, k3_tmap_1(A_308, B_306, C_305, C_305, D_307)) | ~m1_subset_1(D_307, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_305), u1_struct_0(B_306)))) | ~v1_funct_2(D_307, u1_struct_0(C_305), u1_struct_0(B_306)) | ~v1_funct_1(D_307) | ~m1_pre_topc(C_305, A_308) | v2_struct_0(C_305) | ~l1_pre_topc(B_306) | ~v2_pre_topc(B_306) | v2_struct_0(B_306) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308) | v2_struct_0(A_308))), inference(cnfTransformation, [status(thm)], [f_295])).
% 9.58/3.19  tff(c_349, plain, (![A_308]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_308, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_308) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308) | v2_struct_0(A_308))), inference(resolution, [status(thm)], [c_58, c_345])).
% 9.58/3.19  tff(c_353, plain, (![A_308]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_308, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_308) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308) | v2_struct_0(A_308))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_62, c_60, c_349])).
% 9.58/3.19  tff(c_355, plain, (![A_309]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_309, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_309) | ~l1_pre_topc(A_309) | ~v2_pre_topc(A_309) | v2_struct_0(A_309))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_353])).
% 9.58/3.19  tff(c_14, plain, (![D_21, C_20, A_18, B_19]: (D_21=C_20 | ~r2_funct_2(A_18, B_19, C_20, D_21) | ~m1_subset_1(D_21, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_2(D_21, A_18, B_19) | ~v1_funct_1(D_21) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_2(C_20, A_18, B_19) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.58/3.19  tff(c_357, plain, (![A_309]: (k3_tmap_1(A_309, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1(k3_tmap_1(A_309, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1(A_309, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_309, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_309) | ~l1_pre_topc(A_309) | ~v2_pre_topc(A_309) | v2_struct_0(A_309))), inference(resolution, [status(thm)], [c_355, c_14])).
% 9.58/3.19  tff(c_396, plain, (![A_322]: (k3_tmap_1(A_322, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1(k3_tmap_1(A_322, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1(A_322, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_322, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_322) | ~l1_pre_topc(A_322) | ~v2_pre_topc(A_322) | v2_struct_0(A_322))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_357])).
% 9.58/3.19  tff(c_400, plain, (![A_81]: (k3_tmap_1(A_81, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_81, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_81, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_81) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_26, c_396])).
% 9.58/3.19  tff(c_403, plain, (![A_81]: (k3_tmap_1(A_81, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_81, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_81, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_81) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_62, c_60, c_58, c_400])).
% 9.58/3.19  tff(c_405, plain, (![A_323]: (k3_tmap_1(A_323, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_323, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_323, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_323) | ~l1_pre_topc(A_323) | ~v2_pre_topc(A_323) | v2_struct_0(A_323))), inference(negUnitSimplification, [status(thm)], [c_72, c_403])).
% 9.58/3.19  tff(c_411, plain, (![A_324]: (k3_tmap_1(A_324, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_1(k3_tmap_1(A_324, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_324) | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324))), inference(resolution, [status(thm)], [c_343, c_405])).
% 9.58/3.19  tff(c_417, plain, (![A_325]: (k3_tmap_1(A_325, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_pre_topc('#skF_4', A_325) | ~l1_pre_topc(A_325) | ~v2_pre_topc(A_325) | v2_struct_0(A_325))), inference(resolution, [status(thm)], [c_304, c_411])).
% 9.58/3.19  tff(c_421, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_40, c_417])).
% 9.58/3.19  tff(c_427, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_100, c_421])).
% 9.58/3.19  tff(c_428, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_427])).
% 9.58/3.19  tff(c_1051, plain, (![E_397, A_396, D_398, B_400, C_399]: (k3_tmap_1(A_396, B_400, C_399, D_398, E_397)=k2_partfun1(u1_struct_0(C_399), u1_struct_0(B_400), E_397, u1_struct_0(D_398)) | ~m1_pre_topc(D_398, C_399) | ~m1_subset_1(E_397, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_399), u1_struct_0(B_400)))) | ~v1_funct_2(E_397, u1_struct_0(C_399), u1_struct_0(B_400)) | ~v1_funct_1(E_397) | ~m1_pre_topc(D_398, A_396) | ~m1_pre_topc(C_399, A_396) | ~l1_pre_topc(B_400) | ~v2_pre_topc(B_400) | v2_struct_0(B_400) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396))), inference(cnfTransformation, [status(thm)], [f_165])).
% 9.58/3.19  tff(c_1057, plain, (![A_396, D_398]: (k3_tmap_1(A_396, '#skF_3', '#skF_4', D_398, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_398)) | ~m1_pre_topc(D_398, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_398, A_396) | ~m1_pre_topc('#skF_4', A_396) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396))), inference(resolution, [status(thm)], [c_58, c_1051])).
% 9.58/3.19  tff(c_1062, plain, (![A_396, D_398]: (k3_tmap_1(A_396, '#skF_3', '#skF_4', D_398, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_398)) | ~m1_pre_topc(D_398, '#skF_4') | ~m1_pre_topc(D_398, A_396) | ~m1_pre_topc('#skF_4', A_396) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_62, c_60, c_1057])).
% 9.58/3.19  tff(c_1064, plain, (![A_401, D_402]: (k3_tmap_1(A_401, '#skF_3', '#skF_4', D_402, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_402)) | ~m1_pre_topc(D_402, '#skF_4') | ~m1_pre_topc(D_402, A_401) | ~m1_pre_topc('#skF_4', A_401) | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | v2_struct_0(A_401))), inference(negUnitSimplification, [status(thm)], [c_72, c_1062])).
% 9.58/3.19  tff(c_1068, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_521, c_1064])).
% 9.58/3.19  tff(c_1079, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_84, c_521, c_428, c_1068])).
% 9.58/3.19  tff(c_1080, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_1079])).
% 9.58/3.19  tff(c_315, plain, (![A_293, B_294, C_295, D_296]: (k2_partfun1(u1_struct_0(A_293), u1_struct_0(B_294), C_295, u1_struct_0(D_296))=k2_tmap_1(A_293, B_294, C_295, D_296) | ~m1_pre_topc(D_296, A_293) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_293), u1_struct_0(B_294)))) | ~v1_funct_2(C_295, u1_struct_0(A_293), u1_struct_0(B_294)) | ~v1_funct_1(C_295) | ~l1_pre_topc(B_294) | ~v2_pre_topc(B_294) | v2_struct_0(B_294) | ~l1_pre_topc(A_293) | ~v2_pre_topc(A_293) | v2_struct_0(A_293))), inference(cnfTransformation, [status(thm)], [f_133])).
% 9.58/3.19  tff(c_319, plain, (![D_296]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_296))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_296) | ~m1_pre_topc(D_296, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_315])).
% 9.58/3.19  tff(c_323, plain, (![D_296]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_296))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_296) | ~m1_pre_topc(D_296, '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_84, c_70, c_68, c_62, c_60, c_319])).
% 9.58/3.19  tff(c_324, plain, (![D_296]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_296))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_296) | ~m1_pre_topc(D_296, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_72, c_323])).
% 9.58/3.19  tff(c_1089, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1080, c_324])).
% 9.58/3.19  tff(c_1096, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_521, c_1089])).
% 9.58/3.19  tff(c_1397, plain, (![C_427, B_425, D_424, A_426, E_423]: (r2_hidden('#skF_2'(E_423, D_424, B_425, A_426, C_427), u1_struct_0(C_427)) | r2_funct_2(u1_struct_0(C_427), u1_struct_0(A_426), k2_tmap_1(B_425, A_426, D_424, C_427), E_423) | ~m1_subset_1(E_423, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_427), u1_struct_0(A_426)))) | ~v1_funct_2(E_423, u1_struct_0(C_427), u1_struct_0(A_426)) | ~v1_funct_1(E_423) | ~m1_subset_1(D_424, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_425), u1_struct_0(A_426)))) | ~v1_funct_2(D_424, u1_struct_0(B_425), u1_struct_0(A_426)) | ~v1_funct_1(D_424) | ~m1_pre_topc(C_427, B_425) | v2_struct_0(C_427) | ~l1_pre_topc(B_425) | ~v2_pre_topc(B_425) | v2_struct_0(B_425) | ~l1_pre_topc(A_426) | ~v2_pre_topc(A_426) | v2_struct_0(A_426))), inference(cnfTransformation, [status(thm)], [f_265])).
% 9.58/3.19  tff(c_2079, plain, (![A_512, B_513, D_514, B_515]: (r2_hidden('#skF_2'(k4_tmap_1(A_512, B_513), D_514, B_515, A_512, B_513), u1_struct_0(B_513)) | r2_funct_2(u1_struct_0(B_513), u1_struct_0(A_512), k2_tmap_1(B_515, A_512, D_514, B_513), k4_tmap_1(A_512, B_513)) | ~v1_funct_2(k4_tmap_1(A_512, B_513), u1_struct_0(B_513), u1_struct_0(A_512)) | ~v1_funct_1(k4_tmap_1(A_512, B_513)) | ~m1_subset_1(D_514, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_515), u1_struct_0(A_512)))) | ~v1_funct_2(D_514, u1_struct_0(B_515), u1_struct_0(A_512)) | ~v1_funct_1(D_514) | ~m1_pre_topc(B_513, B_515) | v2_struct_0(B_513) | ~l1_pre_topc(B_515) | ~v2_pre_topc(B_515) | v2_struct_0(B_515) | ~m1_pre_topc(B_513, A_512) | ~l1_pre_topc(A_512) | ~v2_pre_topc(A_512) | v2_struct_0(A_512))), inference(resolution, [status(thm)], [c_32, c_1397])).
% 9.58/3.19  tff(c_2084, plain, (r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4', '#skF_3', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1096, c_2079])).
% 9.58/3.19  tff(c_2087, plain, (r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4', '#skF_3', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_100, c_84, c_521, c_62, c_60, c_58, c_2084])).
% 9.58/3.19  tff(c_2088, plain, (r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4', '#skF_3', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_2087])).
% 9.58/3.19  tff(c_2089, plain, (~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2088])).
% 9.58/3.19  tff(c_2092, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_2089])).
% 9.58/3.19  tff(c_2095, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_2092])).
% 9.58/3.19  tff(c_2097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_2095])).
% 9.58/3.19  tff(c_2099, plain, (v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_2088])).
% 9.58/3.19  tff(c_34, plain, (![A_86, B_87]: (v1_funct_2(k4_tmap_1(A_86, B_87), u1_struct_0(B_87), u1_struct_0(A_86)) | ~m1_pre_topc(B_87, A_86) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_210])).
% 9.58/3.19  tff(c_2098, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_2088])).
% 9.58/3.19  tff(c_2118, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_2098])).
% 9.58/3.19  tff(c_2121, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_2118])).
% 9.58/3.19  tff(c_2124, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_2121])).
% 9.58/3.19  tff(c_2126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_2124])).
% 9.58/3.19  tff(c_2128, plain, (v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_2098])).
% 9.58/3.19  tff(c_2127, plain, (r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4', '#skF_3', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_2098])).
% 9.58/3.19  tff(c_2129, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2127])).
% 9.58/3.19  tff(c_2131, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_2129, c_14])).
% 9.58/3.19  tff(c_2134, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2099, c_2128, c_2131])).
% 9.58/3.19  tff(c_2162, plain, (~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_2134])).
% 9.58/3.19  tff(c_2165, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_2162])).
% 9.58/3.19  tff(c_2168, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_2165])).
% 9.58/3.19  tff(c_2170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_2168])).
% 9.58/3.19  tff(c_2171, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_2134])).
% 9.58/3.19  tff(c_2176, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2171, c_54])).
% 9.58/3.19  tff(c_2182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_2176])).
% 9.58/3.19  tff(c_2183, plain, (r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_2127])).
% 9.58/3.19  tff(c_520, plain, (![C_326]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5') | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_326, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_326))), inference(splitRight, [status(thm)], [c_498])).
% 9.58/3.19  tff(c_556, plain, (![C_334]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_334, '#skF_5'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_334, '#skF_5') | ~m1_subset_1(C_334, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_334, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_334))), inference(splitRight, [status(thm)], [c_498])).
% 9.58/3.19  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.58/3.19  tff(c_158, plain, (![A_234, B_235, C_236]: (k1_funct_1(k4_tmap_1(A_234, B_235), C_236)=C_236 | ~r2_hidden(C_236, u1_struct_0(B_235)) | ~m1_subset_1(C_236, u1_struct_0(A_234)) | ~m1_pre_topc(B_235, A_234) | v2_struct_0(B_235) | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234) | v2_struct_0(A_234))), inference(cnfTransformation, [status(thm)], [f_327])).
% 9.58/3.19  tff(c_162, plain, (![A_234, B_235, A_1]: (k1_funct_1(k4_tmap_1(A_234, B_235), A_1)=A_1 | ~m1_subset_1(A_1, u1_struct_0(A_234)) | ~m1_pre_topc(B_235, A_234) | v2_struct_0(B_235) | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234) | v2_struct_0(A_234) | v1_xboole_0(u1_struct_0(B_235)) | ~m1_subset_1(A_1, u1_struct_0(B_235)))), inference(resolution, [status(thm)], [c_2, c_158])).
% 9.58/3.19  tff(c_560, plain, (![B_235, C_334]: (k1_funct_1(k4_tmap_1('#skF_3', B_235), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_334, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_334, '#skF_5') | ~m1_pre_topc(B_235, '#skF_3') | v2_struct_0(B_235) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0(B_235)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_334, '#skF_5'), u1_struct_0(B_235)) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_334, '#skF_5') | ~m1_subset_1(C_334, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_334, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_334))), inference(resolution, [status(thm)], [c_556, c_162])).
% 9.58/3.19  tff(c_569, plain, (![B_235, C_334]: (k1_funct_1(k4_tmap_1('#skF_3', B_235), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_334, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_334, '#skF_5') | ~m1_pre_topc(B_235, '#skF_3') | v2_struct_0(B_235) | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0(B_235)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_334, '#skF_5'), u1_struct_0(B_235)) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_334, '#skF_5') | ~m1_subset_1(C_334, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_334, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_334))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_560])).
% 9.58/3.19  tff(c_647, plain, (![B_343, C_344]: (k1_funct_1(k4_tmap_1('#skF_3', B_343), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_344, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_344, '#skF_5') | ~m1_pre_topc(B_343, '#skF_3') | v2_struct_0(B_343) | v1_xboole_0(u1_struct_0(B_343)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_344, '#skF_5'), u1_struct_0(B_343)) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_344, '#skF_5') | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_344, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_344))), inference(negUnitSimplification, [status(thm)], [c_72, c_569])).
% 9.58/3.19  tff(c_653, plain, (![C_326]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_3'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5') | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_326, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_326))), inference(resolution, [status(thm)], [c_520, c_647])).
% 9.58/3.19  tff(c_663, plain, (![C_326]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_3'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_3') | v1_xboole_0(u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5') | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_326, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_326))), inference(negUnitSimplification, [status(thm)], [c_72, c_653])).
% 9.58/3.19  tff(c_710, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_663])).
% 9.58/3.19  tff(c_726, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_710])).
% 9.58/3.19  tff(c_730, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_726])).
% 9.58/3.19  tff(c_731, plain, (![C_326]: (v1_xboole_0(u1_struct_0('#skF_3')) | k1_funct_1(k4_tmap_1('#skF_3', '#skF_3'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_326, '#skF_5') | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_326, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_326))), inference(splitRight, [status(thm)], [c_663])).
% 9.58/3.19  tff(c_778, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_731])).
% 9.58/3.19  tff(c_101, plain, (![B_205, A_206]: (m1_subset_1(u1_struct_0(B_205), k1_zfmisc_1(u1_struct_0(A_206))) | ~m1_pre_topc(B_205, A_206) | ~l1_pre_topc(A_206))), inference(cnfTransformation, [status(thm)], [f_217])).
% 9.58/3.19  tff(c_4, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.58/3.19  tff(c_104, plain, (![A_206, A_3, B_205]: (~v1_xboole_0(u1_struct_0(A_206)) | ~r2_hidden(A_3, u1_struct_0(B_205)) | ~m1_pre_topc(B_205, A_206) | ~l1_pre_topc(A_206))), inference(resolution, [status(thm)], [c_101, c_4])).
% 9.58/3.19  tff(c_800, plain, (![A_3, B_205]: (~r2_hidden(A_3, u1_struct_0(B_205)) | ~m1_pre_topc(B_205, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_778, c_104])).
% 9.58/3.19  tff(c_803, plain, (![A_3, B_205]: (~r2_hidden(A_3, u1_struct_0(B_205)) | ~m1_pre_topc(B_205, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_800])).
% 9.58/3.19  tff(c_2207, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_2183, c_803])).
% 9.58/3.19  tff(c_2225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_2207])).
% 9.58/3.19  tff(c_2242, plain, (![C_524]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_3'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_524, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_524, '#skF_5') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_524, '#skF_5') | ~m1_subset_1(C_524, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_524, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_524))), inference(splitRight, [status(thm)], [c_731])).
% 9.58/3.19  tff(c_2250, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_3'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_2242])).
% 9.58/3.19  tff(c_2260, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_3'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_2250])).
% 9.58/3.19  tff(c_2261, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_3'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_54, c_2260])).
% 9.58/3.19  tff(c_2265, plain, (~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2261])).
% 9.58/3.19  tff(c_2281, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_2265])).
% 9.58/3.19  tff(c_2284, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_2281])).
% 9.58/3.19  tff(c_2286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_2284])).
% 9.58/3.19  tff(c_2288, plain, (v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_2261])).
% 9.58/3.19  tff(c_2287, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | k1_funct_1(k4_tmap_1('#skF_3', '#skF_3'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_2261])).
% 9.58/3.19  tff(c_2289, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_2287])).
% 9.58/3.19  tff(c_2313, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_2289])).
% 9.58/3.19  tff(c_2316, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_2313])).
% 9.58/3.19  tff(c_2318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_2316])).
% 9.58/3.19  tff(c_2320, plain, (v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_2287])).
% 9.58/3.19  tff(c_2330, plain, (![D_544, E_543, B_546, C_545, A_542]: (k3_tmap_1(A_542, B_546, C_545, D_544, E_543)=k2_partfun1(u1_struct_0(C_545), u1_struct_0(B_546), E_543, u1_struct_0(D_544)) | ~m1_pre_topc(D_544, C_545) | ~m1_subset_1(E_543, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_545), u1_struct_0(B_546)))) | ~v1_funct_2(E_543, u1_struct_0(C_545), u1_struct_0(B_546)) | ~v1_funct_1(E_543) | ~m1_pre_topc(D_544, A_542) | ~m1_pre_topc(C_545, A_542) | ~l1_pre_topc(B_546) | ~v2_pre_topc(B_546) | v2_struct_0(B_546) | ~l1_pre_topc(A_542) | ~v2_pre_topc(A_542) | v2_struct_0(A_542))), inference(cnfTransformation, [status(thm)], [f_165])).
% 9.58/3.19  tff(c_2336, plain, (![A_542, D_544]: (k3_tmap_1(A_542, '#skF_3', '#skF_4', D_544, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_544)) | ~m1_pre_topc(D_544, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_544, A_542) | ~m1_pre_topc('#skF_4', A_542) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_542) | ~v2_pre_topc(A_542) | v2_struct_0(A_542))), inference(resolution, [status(thm)], [c_58, c_2330])).
% 9.58/3.19  tff(c_2341, plain, (![A_542, D_544]: (k3_tmap_1(A_542, '#skF_3', '#skF_4', D_544, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_544)) | ~m1_pre_topc(D_544, '#skF_4') | ~m1_pre_topc(D_544, A_542) | ~m1_pre_topc('#skF_4', A_542) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_542) | ~v2_pre_topc(A_542) | v2_struct_0(A_542))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_62, c_60, c_2336])).
% 9.58/3.19  tff(c_2343, plain, (![A_547, D_548]: (k3_tmap_1(A_547, '#skF_3', '#skF_4', D_548, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_548)) | ~m1_pre_topc(D_548, '#skF_4') | ~m1_pre_topc(D_548, A_547) | ~m1_pre_topc('#skF_4', A_547) | ~l1_pre_topc(A_547) | ~v2_pre_topc(A_547) | v2_struct_0(A_547))), inference(negUnitSimplification, [status(thm)], [c_72, c_2341])).
% 9.58/3.19  tff(c_2347, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_521, c_2343])).
% 9.58/3.19  tff(c_2358, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_84, c_521, c_428, c_2347])).
% 9.58/3.19  tff(c_2359, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_2358])).
% 9.58/3.19  tff(c_2368, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2359, c_324])).
% 9.58/3.19  tff(c_2375, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_521, c_2368])).
% 9.58/3.19  tff(c_2509, plain, (![B_554, A_555, E_552, C_556, D_553]: (m1_subset_1('#skF_2'(E_552, D_553, B_554, A_555, C_556), u1_struct_0(B_554)) | r2_funct_2(u1_struct_0(C_556), u1_struct_0(A_555), k2_tmap_1(B_554, A_555, D_553, C_556), E_552) | ~m1_subset_1(E_552, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_556), u1_struct_0(A_555)))) | ~v1_funct_2(E_552, u1_struct_0(C_556), u1_struct_0(A_555)) | ~v1_funct_1(E_552) | ~m1_subset_1(D_553, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_554), u1_struct_0(A_555)))) | ~v1_funct_2(D_553, u1_struct_0(B_554), u1_struct_0(A_555)) | ~v1_funct_1(D_553) | ~m1_pre_topc(C_556, B_554) | v2_struct_0(C_556) | ~l1_pre_topc(B_554) | ~v2_pre_topc(B_554) | v2_struct_0(B_554) | ~l1_pre_topc(A_555) | ~v2_pre_topc(A_555) | v2_struct_0(A_555))), inference(cnfTransformation, [status(thm)], [f_265])).
% 9.58/3.19  tff(c_3495, plain, (![A_652, B_653, D_654, B_655]: (m1_subset_1('#skF_2'(k4_tmap_1(A_652, B_653), D_654, B_655, A_652, B_653), u1_struct_0(B_655)) | r2_funct_2(u1_struct_0(B_653), u1_struct_0(A_652), k2_tmap_1(B_655, A_652, D_654, B_653), k4_tmap_1(A_652, B_653)) | ~v1_funct_2(k4_tmap_1(A_652, B_653), u1_struct_0(B_653), u1_struct_0(A_652)) | ~v1_funct_1(k4_tmap_1(A_652, B_653)) | ~m1_subset_1(D_654, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_655), u1_struct_0(A_652)))) | ~v1_funct_2(D_654, u1_struct_0(B_655), u1_struct_0(A_652)) | ~v1_funct_1(D_654) | ~m1_pre_topc(B_653, B_655) | v2_struct_0(B_653) | ~l1_pre_topc(B_655) | ~v2_pre_topc(B_655) | v2_struct_0(B_655) | ~m1_pre_topc(B_653, A_652) | ~l1_pre_topc(A_652) | ~v2_pre_topc(A_652) | v2_struct_0(A_652))), inference(resolution, [status(thm)], [c_32, c_2509])).
% 9.58/3.19  tff(c_3509, plain, (m1_subset_1('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4', '#skF_3', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2375, c_3495])).
% 9.58/3.19  tff(c_3516, plain, (m1_subset_1('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4', '#skF_3', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_100, c_84, c_521, c_62, c_60, c_58, c_2288, c_2320, c_3509])).
% 9.58/3.19  tff(c_3517, plain, (m1_subset_1('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4', '#skF_3', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_3516])).
% 9.58/3.19  tff(c_3518, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_3517])).
% 9.58/3.19  tff(c_3520, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_3518, c_14])).
% 9.58/3.19  tff(c_3523, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2288, c_2320, c_3520])).
% 9.58/3.19  tff(c_3524, plain, (~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_3523])).
% 9.58/3.19  tff(c_3545, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_3524])).
% 9.58/3.19  tff(c_3548, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_3545])).
% 9.58/3.19  tff(c_3550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3548])).
% 9.58/3.19  tff(c_3551, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_3523])).
% 9.58/3.19  tff(c_3559, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3551, c_54])).
% 9.58/3.19  tff(c_3565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_3559])).
% 9.58/3.19  tff(c_3567, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_3517])).
% 9.58/3.19  tff(c_2692, plain, (![E_569, C_573, D_570, B_571, A_572]: (r2_hidden('#skF_2'(E_569, D_570, B_571, A_572, C_573), u1_struct_0(C_573)) | r2_funct_2(u1_struct_0(C_573), u1_struct_0(A_572), k2_tmap_1(B_571, A_572, D_570, C_573), E_569) | ~m1_subset_1(E_569, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_573), u1_struct_0(A_572)))) | ~v1_funct_2(E_569, u1_struct_0(C_573), u1_struct_0(A_572)) | ~v1_funct_1(E_569) | ~m1_subset_1(D_570, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_571), u1_struct_0(A_572)))) | ~v1_funct_2(D_570, u1_struct_0(B_571), u1_struct_0(A_572)) | ~v1_funct_1(D_570) | ~m1_pre_topc(C_573, B_571) | v2_struct_0(C_573) | ~l1_pre_topc(B_571) | ~v2_pre_topc(B_571) | v2_struct_0(B_571) | ~l1_pre_topc(A_572) | ~v2_pre_topc(A_572) | v2_struct_0(A_572))), inference(cnfTransformation, [status(thm)], [f_265])).
% 9.58/3.19  tff(c_3602, plain, (![A_659, B_660, D_661, B_662]: (r2_hidden('#skF_2'(k4_tmap_1(A_659, B_660), D_661, B_662, A_659, B_660), u1_struct_0(B_660)) | r2_funct_2(u1_struct_0(B_660), u1_struct_0(A_659), k2_tmap_1(B_662, A_659, D_661, B_660), k4_tmap_1(A_659, B_660)) | ~v1_funct_2(k4_tmap_1(A_659, B_660), u1_struct_0(B_660), u1_struct_0(A_659)) | ~v1_funct_1(k4_tmap_1(A_659, B_660)) | ~m1_subset_1(D_661, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_662), u1_struct_0(A_659)))) | ~v1_funct_2(D_661, u1_struct_0(B_662), u1_struct_0(A_659)) | ~v1_funct_1(D_661) | ~m1_pre_topc(B_660, B_662) | v2_struct_0(B_660) | ~l1_pre_topc(B_662) | ~v2_pre_topc(B_662) | v2_struct_0(B_662) | ~m1_pre_topc(B_660, A_659) | ~l1_pre_topc(A_659) | ~v2_pre_topc(A_659) | v2_struct_0(A_659))), inference(resolution, [status(thm)], [c_32, c_2692])).
% 9.58/3.19  tff(c_3607, plain, (r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4', '#skF_3', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2375, c_3602])).
% 9.58/3.19  tff(c_3610, plain, (r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4', '#skF_3', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_100, c_84, c_521, c_62, c_60, c_58, c_2288, c_2320, c_3607])).
% 9.58/3.19  tff(c_3611, plain, (r2_hidden('#skF_2'(k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_3567, c_3610])).
% 9.58/3.19  tff(c_106, plain, (![D_207]: (k1_funct_1('#skF_5', D_207)=D_207 | ~r2_hidden(D_207, u1_struct_0('#skF_4')) | ~m1_subset_1(D_207, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_357])).
% 9.58/3.19  tff(c_111, plain, (![A_1]: (k1_funct_1('#skF_5', A_1)=A_1 | ~m1_subset_1(A_1, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_1, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2, c_106])).
% 9.58/3.19  tff(c_129, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_111])).
% 9.58/3.19  tff(c_132, plain, (![A_3, B_205]: (~r2_hidden(A_3, u1_struct_0(B_205)) | ~m1_pre_topc(B_205, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_129, c_104])).
% 9.58/3.19  tff(c_135, plain, (![A_3, B_205]: (~r2_hidden(A_3, u1_struct_0(B_205)) | ~m1_pre_topc(B_205, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_132])).
% 9.58/3.19  tff(c_3620, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_3611, c_135])).
% 9.58/3.19  tff(c_3632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_521, c_3620])).
% 9.58/3.19  tff(c_3633, plain, (![A_1]: (k1_funct_1('#skF_5', A_1)=A_1 | ~m1_subset_1(A_1, u1_struct_0('#skF_3')) | ~m1_subset_1(A_1, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_111])).
% 9.58/3.19  tff(c_3714, plain, (![C_699]: (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_699, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_699, '#skF_5') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_699, '#skF_5'), u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_699, '#skF_5') | ~m1_subset_1(C_699, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_699, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_699))), inference(resolution, [status(thm)], [c_3704, c_3633])).
% 9.58/3.19  tff(c_3720, plain, (![C_699]: (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_699, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_699, '#skF_5') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_699, '#skF_5'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_3') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_699, '#skF_5') | ~m1_subset_1(C_699, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_699, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_699))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_3714])).
% 9.58/3.19  tff(c_3838, plain, (![C_751]: (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_751, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_751, '#skF_5') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_751, '#skF_5'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_751, '#skF_5') | ~m1_subset_1(C_751, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_751, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_751))), inference(negUnitSimplification, [status(thm)], [c_72, c_3720])).
% 9.58/3.19  tff(c_3929, plain, (![C_754]: (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_754, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_754, '#skF_5') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_754, '#skF_5') | ~m1_subset_1(C_754, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_754, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_754))), inference(resolution, [status(thm)], [c_3678, c_3838])).
% 9.58/3.19  tff(c_3937, plain, (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_3929])).
% 9.58/3.19  tff(c_3947, plain, (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_3937])).
% 9.58/3.19  tff(c_3948, plain, (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_54, c_3947])).
% 9.58/3.19  tff(c_3985, plain, (~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_3948])).
% 9.58/3.19  tff(c_4016, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_3985])).
% 9.58/3.19  tff(c_4019, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_4016])).
% 9.58/3.19  tff(c_4021, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_4019])).
% 9.58/3.19  tff(c_4023, plain, (v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_3948])).
% 9.58/3.19  tff(c_4022, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_3948])).
% 9.58/3.19  tff(c_4148, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_4022])).
% 9.58/3.19  tff(c_4151, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_4148])).
% 9.58/3.19  tff(c_4154, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_4151])).
% 9.58/3.19  tff(c_4156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_4154])).
% 9.58/3.19  tff(c_4158, plain, (v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_4022])).
% 9.58/3.19  tff(c_4157, plain, (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_4022])).
% 9.58/3.19  tff(c_3634, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_111])).
% 9.58/3.19  tff(c_3722, plain, (![E_702, A_701, C_703, B_705, D_704]: (v1_funct_1(k3_tmap_1(A_701, B_705, C_703, D_704, E_702)) | ~m1_subset_1(E_702, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_703), u1_struct_0(B_705)))) | ~v1_funct_2(E_702, u1_struct_0(C_703), u1_struct_0(B_705)) | ~v1_funct_1(E_702) | ~m1_pre_topc(D_704, A_701) | ~m1_pre_topc(C_703, A_701) | ~l1_pre_topc(B_705) | ~v2_pre_topc(B_705) | v2_struct_0(B_705) | ~l1_pre_topc(A_701) | ~v2_pre_topc(A_701) | v2_struct_0(A_701))), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.58/3.19  tff(c_3726, plain, (![A_701, D_704]: (v1_funct_1(k3_tmap_1(A_701, '#skF_3', '#skF_4', D_704, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_704, A_701) | ~m1_pre_topc('#skF_4', A_701) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_701) | ~v2_pre_topc(A_701) | v2_struct_0(A_701))), inference(resolution, [status(thm)], [c_58, c_3722])).
% 9.58/3.19  tff(c_3730, plain, (![A_701, D_704]: (v1_funct_1(k3_tmap_1(A_701, '#skF_3', '#skF_4', D_704, '#skF_5')) | ~m1_pre_topc(D_704, A_701) | ~m1_pre_topc('#skF_4', A_701) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_701) | ~v2_pre_topc(A_701) | v2_struct_0(A_701))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_62, c_60, c_3726])).
% 9.58/3.19  tff(c_3731, plain, (![A_701, D_704]: (v1_funct_1(k3_tmap_1(A_701, '#skF_3', '#skF_4', D_704, '#skF_5')) | ~m1_pre_topc(D_704, A_701) | ~m1_pre_topc('#skF_4', A_701) | ~l1_pre_topc(A_701) | ~v2_pre_topc(A_701) | v2_struct_0(A_701))), inference(negUnitSimplification, [status(thm)], [c_72, c_3730])).
% 9.58/3.19  tff(c_3777, plain, (![A_730, D_733, B_734, C_732, E_731]: (v1_funct_2(k3_tmap_1(A_730, B_734, C_732, D_733, E_731), u1_struct_0(D_733), u1_struct_0(B_734)) | ~m1_subset_1(E_731, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_732), u1_struct_0(B_734)))) | ~v1_funct_2(E_731, u1_struct_0(C_732), u1_struct_0(B_734)) | ~v1_funct_1(E_731) | ~m1_pre_topc(D_733, A_730) | ~m1_pre_topc(C_732, A_730) | ~l1_pre_topc(B_734) | ~v2_pre_topc(B_734) | v2_struct_0(B_734) | ~l1_pre_topc(A_730) | ~v2_pre_topc(A_730) | v2_struct_0(A_730))), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.58/3.19  tff(c_3781, plain, (![A_730, D_733]: (v1_funct_2(k3_tmap_1(A_730, '#skF_3', '#skF_4', D_733, '#skF_5'), u1_struct_0(D_733), u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_733, A_730) | ~m1_pre_topc('#skF_4', A_730) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_730) | ~v2_pre_topc(A_730) | v2_struct_0(A_730))), inference(resolution, [status(thm)], [c_58, c_3777])).
% 9.58/3.19  tff(c_3785, plain, (![A_730, D_733]: (v1_funct_2(k3_tmap_1(A_730, '#skF_3', '#skF_4', D_733, '#skF_5'), u1_struct_0(D_733), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_733, A_730) | ~m1_pre_topc('#skF_4', A_730) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_730) | ~v2_pre_topc(A_730) | v2_struct_0(A_730))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_62, c_60, c_3781])).
% 9.58/3.19  tff(c_3786, plain, (![A_730, D_733]: (v1_funct_2(k3_tmap_1(A_730, '#skF_3', '#skF_4', D_733, '#skF_5'), u1_struct_0(D_733), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_733, A_730) | ~m1_pre_topc('#skF_4', A_730) | ~l1_pre_topc(A_730) | ~v2_pre_topc(A_730) | v2_struct_0(A_730))), inference(negUnitSimplification, [status(thm)], [c_72, c_3785])).
% 9.58/3.19  tff(c_3761, plain, (![C_725, B_726, D_727, A_728]: (r2_funct_2(u1_struct_0(C_725), u1_struct_0(B_726), D_727, k3_tmap_1(A_728, B_726, C_725, C_725, D_727)) | ~m1_subset_1(D_727, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_725), u1_struct_0(B_726)))) | ~v1_funct_2(D_727, u1_struct_0(C_725), u1_struct_0(B_726)) | ~v1_funct_1(D_727) | ~m1_pre_topc(C_725, A_728) | v2_struct_0(C_725) | ~l1_pre_topc(B_726) | ~v2_pre_topc(B_726) | v2_struct_0(B_726) | ~l1_pre_topc(A_728) | ~v2_pre_topc(A_728) | v2_struct_0(A_728))), inference(cnfTransformation, [status(thm)], [f_295])).
% 9.58/3.19  tff(c_3765, plain, (![A_728]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_728, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_728) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_728) | ~v2_pre_topc(A_728) | v2_struct_0(A_728))), inference(resolution, [status(thm)], [c_58, c_3761])).
% 9.58/3.19  tff(c_3769, plain, (![A_728]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_728, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_728) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_728) | ~v2_pre_topc(A_728) | v2_struct_0(A_728))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_62, c_60, c_3765])).
% 9.58/3.19  tff(c_3771, plain, (![A_729]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_729, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_729) | ~l1_pre_topc(A_729) | ~v2_pre_topc(A_729) | v2_struct_0(A_729))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_3769])).
% 9.58/3.19  tff(c_3773, plain, (![A_729]: (k3_tmap_1(A_729, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1(k3_tmap_1(A_729, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1(A_729, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_729, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_729) | ~l1_pre_topc(A_729) | ~v2_pre_topc(A_729) | v2_struct_0(A_729))), inference(resolution, [status(thm)], [c_3771, c_14])).
% 9.58/3.19  tff(c_3823, plain, (![A_749]: (k3_tmap_1(A_749, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1(k3_tmap_1(A_749, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1(A_749, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_749, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_749) | ~l1_pre_topc(A_749) | ~v2_pre_topc(A_749) | v2_struct_0(A_749))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_3773])).
% 9.58/3.19  tff(c_3827, plain, (![A_81]: (k3_tmap_1(A_81, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_81, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_81, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_81) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_26, c_3823])).
% 9.58/3.19  tff(c_3830, plain, (![A_81]: (k3_tmap_1(A_81, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_81, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_81, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_81) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_62, c_60, c_58, c_3827])).
% 9.58/3.19  tff(c_3832, plain, (![A_750]: (k3_tmap_1(A_750, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_750, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_750, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_750) | ~l1_pre_topc(A_750) | ~v2_pre_topc(A_750) | v2_struct_0(A_750))), inference(negUnitSimplification, [status(thm)], [c_72, c_3830])).
% 9.58/3.19  tff(c_3851, plain, (![A_752]: (k3_tmap_1(A_752, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_1(k3_tmap_1(A_752, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_752) | ~l1_pre_topc(A_752) | ~v2_pre_topc(A_752) | v2_struct_0(A_752))), inference(resolution, [status(thm)], [c_3786, c_3832])).
% 9.58/3.19  tff(c_3857, plain, (![A_753]: (k3_tmap_1(A_753, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_pre_topc('#skF_4', A_753) | ~l1_pre_topc(A_753) | ~v2_pre_topc(A_753) | v2_struct_0(A_753))), inference(resolution, [status(thm)], [c_3731, c_3851])).
% 9.58/3.19  tff(c_3864, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_3857])).
% 9.58/3.19  tff(c_3871, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3864])).
% 9.58/3.19  tff(c_3872, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_72, c_3871])).
% 9.58/3.19  tff(c_3952, plain, (![D_757, B_759, A_755, E_756, C_758]: (k3_tmap_1(A_755, B_759, C_758, D_757, E_756)=k2_partfun1(u1_struct_0(C_758), u1_struct_0(B_759), E_756, u1_struct_0(D_757)) | ~m1_pre_topc(D_757, C_758) | ~m1_subset_1(E_756, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_758), u1_struct_0(B_759)))) | ~v1_funct_2(E_756, u1_struct_0(C_758), u1_struct_0(B_759)) | ~v1_funct_1(E_756) | ~m1_pre_topc(D_757, A_755) | ~m1_pre_topc(C_758, A_755) | ~l1_pre_topc(B_759) | ~v2_pre_topc(B_759) | v2_struct_0(B_759) | ~l1_pre_topc(A_755) | ~v2_pre_topc(A_755) | v2_struct_0(A_755))), inference(cnfTransformation, [status(thm)], [f_165])).
% 9.58/3.19  tff(c_3958, plain, (![A_755, D_757]: (k3_tmap_1(A_755, '#skF_3', '#skF_4', D_757, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_757)) | ~m1_pre_topc(D_757, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_757, A_755) | ~m1_pre_topc('#skF_4', A_755) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_755) | ~v2_pre_topc(A_755) | v2_struct_0(A_755))), inference(resolution, [status(thm)], [c_58, c_3952])).
% 9.58/3.19  tff(c_3963, plain, (![A_755, D_757]: (k3_tmap_1(A_755, '#skF_3', '#skF_4', D_757, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_757)) | ~m1_pre_topc(D_757, '#skF_4') | ~m1_pre_topc(D_757, A_755) | ~m1_pre_topc('#skF_4', A_755) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_755) | ~v2_pre_topc(A_755) | v2_struct_0(A_755))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_62, c_60, c_3958])).
% 9.58/3.19  tff(c_3965, plain, (![A_760, D_761]: (k3_tmap_1(A_760, '#skF_3', '#skF_4', D_761, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_761)) | ~m1_pre_topc(D_761, '#skF_4') | ~m1_pre_topc(D_761, A_760) | ~m1_pre_topc('#skF_4', A_760) | ~l1_pre_topc(A_760) | ~v2_pre_topc(A_760) | v2_struct_0(A_760))), inference(negUnitSimplification, [status(thm)], [c_72, c_3963])).
% 9.58/3.19  tff(c_3969, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_3965])).
% 9.58/3.19  tff(c_3973, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_3872, c_3969])).
% 9.58/3.19  tff(c_3974, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_3973])).
% 9.58/3.19  tff(c_3975, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_3974])).
% 9.58/3.19  tff(c_3978, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_40, c_3975])).
% 9.58/3.19  tff(c_3982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_3978])).
% 9.58/3.19  tff(c_3984, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_3974])).
% 9.58/3.19  tff(c_4591, plain, (![C_809, A_810, A_811]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_809, '#skF_5'), u1_struct_0(A_810)) | ~m1_pre_topc(A_811, A_810) | ~l1_pre_topc(A_810) | v2_struct_0(A_810) | ~m1_pre_topc('#skF_4', A_811) | ~l1_pre_topc(A_811) | v2_struct_0(A_811) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_809, '#skF_5') | ~m1_subset_1(C_809, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_809, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_809))), inference(resolution, [status(thm)], [c_3704, c_20])).
% 9.58/3.19  tff(c_4597, plain, (![C_809]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_809, '#skF_5'), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_809, '#skF_5') | ~m1_subset_1(C_809, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_809, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_809))), inference(resolution, [status(thm)], [c_64, c_4591])).
% 9.58/3.19  tff(c_4605, plain, (![C_809]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_809, '#skF_5'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_809, '#skF_5') | ~m1_subset_1(C_809, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_809, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_809))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_3984, c_68, c_4597])).
% 9.58/3.19  tff(c_4607, plain, (![C_812]: (m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_812, '#skF_5'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_812, '#skF_5') | ~m1_subset_1(C_812, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_812, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_812))), inference(negUnitSimplification, [status(thm)], [c_66, c_72, c_4605])).
% 9.58/3.19  tff(c_3652, plain, (![A_677, B_678, C_679]: (k1_funct_1(k4_tmap_1(A_677, B_678), C_679)=C_679 | ~r2_hidden(C_679, u1_struct_0(B_678)) | ~m1_subset_1(C_679, u1_struct_0(A_677)) | ~m1_pre_topc(B_678, A_677) | v2_struct_0(B_678) | ~l1_pre_topc(A_677) | ~v2_pre_topc(A_677) | v2_struct_0(A_677))), inference(cnfTransformation, [status(thm)], [f_327])).
% 9.58/3.19  tff(c_3656, plain, (![A_677, B_678, A_1]: (k1_funct_1(k4_tmap_1(A_677, B_678), A_1)=A_1 | ~m1_subset_1(A_1, u1_struct_0(A_677)) | ~m1_pre_topc(B_678, A_677) | v2_struct_0(B_678) | ~l1_pre_topc(A_677) | ~v2_pre_topc(A_677) | v2_struct_0(A_677) | v1_xboole_0(u1_struct_0(B_678)) | ~m1_subset_1(A_1, u1_struct_0(B_678)))), inference(resolution, [status(thm)], [c_2, c_3652])).
% 9.58/3.19  tff(c_4611, plain, (![B_678, C_812]: (k1_funct_1(k4_tmap_1('#skF_3', B_678), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_812, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_812, '#skF_5') | ~m1_pre_topc(B_678, '#skF_3') | v2_struct_0(B_678) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0(B_678)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_812, '#skF_5'), u1_struct_0(B_678)) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_812, '#skF_5') | ~m1_subset_1(C_812, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_812, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_812))), inference(resolution, [status(thm)], [c_4607, c_3656])).
% 9.58/3.19  tff(c_4620, plain, (![B_678, C_812]: (k1_funct_1(k4_tmap_1('#skF_3', B_678), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_812, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_812, '#skF_5') | ~m1_pre_topc(B_678, '#skF_3') | v2_struct_0(B_678) | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0(B_678)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_812, '#skF_5'), u1_struct_0(B_678)) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_812, '#skF_5') | ~m1_subset_1(C_812, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_812, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_812))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_4611])).
% 9.58/3.19  tff(c_5282, plain, (![B_886, C_887]: (k1_funct_1(k4_tmap_1('#skF_3', B_886), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_887, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_887, '#skF_5') | ~m1_pre_topc(B_886, '#skF_3') | v2_struct_0(B_886) | v1_xboole_0(u1_struct_0(B_886)) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_887, '#skF_5'), u1_struct_0(B_886)) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_887, '#skF_5') | ~m1_subset_1(C_887, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_887, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_887))), inference(negUnitSimplification, [status(thm)], [c_72, c_4620])).
% 9.58/3.19  tff(c_5294, plain, (![C_691]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_691, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_691, '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_691, '#skF_5') | ~m1_subset_1(C_691, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_691, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_691))), inference(resolution, [status(thm)], [c_3678, c_5282])).
% 9.58/3.19  tff(c_5302, plain, (![C_691]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_691, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_691, '#skF_5') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_691, '#skF_5') | ~m1_subset_1(C_691, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_691, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_691))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5294])).
% 9.58/3.19  tff(c_5304, plain, (![C_888]: (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_888, '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_888, '#skF_5') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), C_888, '#skF_5') | ~m1_subset_1(C_888, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(C_888, u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(C_888))), inference(negUnitSimplification, [status(thm)], [c_3634, c_66, c_5302])).
% 9.58/3.19  tff(c_5324, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_5304])).
% 9.58/3.19  tff(c_5346, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_4023, c_4158, c_5324])).
% 9.58/3.19  tff(c_5347, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_54, c_5346])).
% 9.58/3.19  tff(c_8, plain, (![D_14, A_6, B_7, C_8]: (k1_funct_1(D_14, '#skF_1'(A_6, B_7, C_8, D_14))!=k1_funct_1(C_8, '#skF_1'(A_6, B_7, C_8, D_14)) | r2_funct_2(A_6, B_7, C_8, D_14) | ~m1_subset_1(D_14, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))) | ~v1_funct_2(D_14, A_6, B_7) | ~v1_funct_1(D_14) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))) | ~v1_funct_2(C_8, A_6, B_7) | ~v1_funct_1(C_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.58/3.19  tff(c_5353, plain, (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5'))!='#skF_1'(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5347, c_8])).
% 9.58/3.19  tff(c_5357, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5') | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_4023, c_4158, c_62, c_60, c_58, c_4157, c_5353])).
% 9.58/3.19  tff(c_5358, plain, (~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_5357])).
% 9.58/3.19  tff(c_5362, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_5358])).
% 9.58/3.19  tff(c_5365, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_5362])).
% 9.58/3.19  tff(c_5367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_5365])).
% 9.58/3.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.58/3.19  
% 9.58/3.19  Inference rules
% 9.58/3.19  ----------------------
% 9.58/3.19  #Ref     : 2
% 9.58/3.19  #Sup     : 1053
% 9.58/3.19  #Fact    : 0
% 9.58/3.19  #Define  : 0
% 9.58/3.19  #Split   : 26
% 9.58/3.19  #Chain   : 0
% 9.58/3.19  #Close   : 0
% 9.58/3.19  
% 9.58/3.19  Ordering : KBO
% 9.58/3.19  
% 9.58/3.19  Simplification rules
% 9.58/3.19  ----------------------
% 9.58/3.19  #Subsume      : 193
% 9.58/3.19  #Demod        : 2714
% 9.58/3.19  #Tautology    : 323
% 9.58/3.19  #SimpNegUnit  : 449
% 9.58/3.19  #BackRed      : 11
% 9.58/3.19  
% 9.58/3.19  #Partial instantiations: 0
% 9.58/3.19  #Strategies tried      : 1
% 9.58/3.19  
% 9.58/3.19  Timing (in seconds)
% 9.58/3.19  ----------------------
% 9.58/3.20  Preprocessing        : 0.42
% 9.58/3.20  Parsing              : 0.22
% 9.58/3.20  CNF conversion       : 0.04
% 9.58/3.20  Main loop            : 1.96
% 9.58/3.20  Inferencing          : 0.67
% 9.58/3.20  Reduction            : 0.59
% 9.58/3.20  Demodulation         : 0.42
% 9.58/3.20  BG Simplification    : 0.07
% 9.58/3.20  Subsumption          : 0.54
% 9.58/3.20  Abstraction          : 0.09
% 9.63/3.20  MUC search           : 0.00
% 9.63/3.20  Cooper               : 0.00
% 9.63/3.20  Total                : 2.48
% 9.63/3.20  Index Insertion      : 0.00
% 9.63/3.20  Index Deletion       : 0.00
% 9.63/3.20  Index Matching       : 0.00
% 9.63/3.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
